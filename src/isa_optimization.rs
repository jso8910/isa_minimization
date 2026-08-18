use std::{
    collections::{HashMap, HashSet},
    fs, mem,
    path::Path,
};

use itertools::Itertools;
use rand::{
    distr::{weighted::WeightedIndex, Distribution},
    seq::{IndexedRandom, IteratorRandom},
    Rng, RngExt,
};
use rayon::prelude::*;

use crate::{
    bit::{Bit, BitPattern},
    constants::{
        P_MUT_CONST_TO_VAR, P_MUT_VAR_TO_NONE, WEIGHT_CORE_SIZE, WEIGHT_UNMODIFIED_PROGRAM,
    },
    instruction_semantics::FieldName,
    isa_specification::{
        instruction_valid_under_field_uses, DecodedInstruction, FieldUses, MergeMode, ISA,
    },
    simulator::{GateOutputAssignment, OptimizationWorkspace, Simulator},
};

const TOP_CANDIDATE_GATELIST_PATH: &str = "outputs/top_candidate.v";

pub struct IsaOptimizationManager<'a, R: Rng> {
    isa: &'a ISA,
    candidates: Vec<ISACandidate>,
    candidate_fitnesses: Vec<f64>,
    rng: R,
    /// Instruction forms which must have at least one valid encoding.
    /// The key represents the instruction name, while the value represents a set of all the forms
    /// which must have at least one valid encoding. If the key exists but the set is empty, that
    /// means at least one form (but not specified which one) for that instruction must have a valid encoding.
    mandatory_forms: HashMap<String, HashSet<String>>,
    /// Instruction forms which must have ALL instructions in the form remain valid - ie none
    /// removed by the new ISA. Intended for branch instructions, which are incredibly difficult if
    /// not impossible to replace with a superoptimizer, as well as the fact that their encoding may
    /// change after superoptimization.
    unrestricted_forms: HashMap<String, HashSet<String>>,
    /// Field uses which candidates must preserve exactly. Used for field-level requirements that
    /// should not force entire forms to be unrestricted.
    fixed_field_uses: HashMap<FieldName, FieldUses>,

    /// Copy of maximal ISA candidate
    max_isa_candidate: ISACandidate,
    netlist_file: String,
    simulator: Simulator,
    program: Vec<DecodedInstruction>,
    optimization_workspace: OptimizationWorkspace,

    /// Population size
    population_size: usize,
    /// Number of elite candidates kept every generation
    elite_candidate_count: usize,
    /// Chance that crossover will occur
    crossover_rate: f64,
    /// Chance that, during crossover, each individual gene will cross over
    crossover_gene_rate: f64,
    /// Chance that each child in the new generation will have any given field mutated.
    mutate_field_rate: f64,
    /// Chance that each child will have active_forms mutated for each instruction
    mutate_form_rate: f64,
}

impl<'a, R: Rng + Sync> IsaOptimizationManager<'a, R> {
    pub fn new(
        isa: &'a ISA,
        rng: R,
        mandatory_forms: HashMap<String, HashSet<String>>,
        unrestricted_forms: HashMap<String, HashSet<String>>,
        netlist_file: &str,
        standard_cell_file: &str,
        program: Vec<DecodedInstruction>,
        population_size: usize,
        elite_candidate_count: usize,
        crossover_rate: f64,
        crossover_gene_rate: f64,
        mutate_field_rate: f64,
        mutate_form_rate: f64,
    ) -> Self {
        let simulator = Simulator::from_file(netlist_file, standard_cell_file);
        let optimization_workspace = simulator.optimization_workspace();

        let max_isa_candidate = ISACandidate::max_isa(isa);

        Self {
            isa,
            candidates: vec![],
            candidate_fitnesses: vec![],
            rng,
            mandatory_forms,
            unrestricted_forms,
            fixed_field_uses: HashMap::new(),
            max_isa_candidate,
            netlist_file: netlist_file.to_string(),
            simulator,
            program,
            optimization_workspace,
            population_size,
            elite_candidate_count,
            crossover_rate,
            crossover_gene_rate,
            mutate_field_rate,
            mutate_form_rate,
        }
    }

    pub fn with_fixed_field_uses(
        mut self,
        fixed_field_uses: HashMap<FieldName, FieldUses>,
    ) -> Self {
        self.fixed_field_uses = fixed_field_uses;
        self
    }

    pub fn optimize(&mut self) {
        let num_generations = 10_000;
        self.set_initial_generation();
        for i in 0..num_generations {
            self.new_generation();
            println!(
                "{:?}",
                self.candidate_fitnesses
                    .clone()
                    .into_iter()
                    .fold(f64::NEG_INFINITY, f64::max)
            );
            let candidate = self
                .candidates
                .iter()
                .zip(self.candidate_fitnesses.iter())
                .max_by(|(_, fitness_a), (_, fitness_b)| fitness_a.total_cmp(fitness_b))
                .map(|(candidate, _)| candidate.clone())
                .unwrap();
            match self.write_top_candidate_gatelist(&candidate) {
                Ok(commented_gate_count) => {
                    println!(
                        "Wrote {TOP_CANDIDATE_GATELIST_PATH} with {commented_gate_count} commented gates"
                    );
                }
                Err(err) => eprintln!("Failed to write {TOP_CANDIDATE_GATELIST_PATH}: {err}"),
            }
            println!("{:#?}", candidate.valid_field_uses);
            println!("{:#?}", candidate.active_forms);
            println!("{i} {:?}", self.gate_removal_count(&candidate).unwrap());
            println!("{:?}", self.instruction_conflict_count(&candidate));
            for instruction in self.program.iter() {
                if !candidate.supports_instruction(instruction) {
                    // println!(
                    //     "{} {:?} {}",
                    //     instruction.name,
                    //     instruction.form.name,
                    //     instruction
                    //         .bits
                    //         .iter()
                    //         .map(|b| match b {
                    //             Bit::High => "1",
                    //             Bit::Low => "0",
                    //             _ => panic!(),
                    //         })
                    //         .collect::<String>()
                    // )
                }
            }
        }
    }

    fn set_initial_generation(&mut self) {
        // We want to seed this with both the maximum possible ISA (with all features) and the
        // minimum ISA which does not break any instructions.
        // This is done because we don't want to just default to removing most of the instructions
        // or default to maintianing functionality, because, with random ISAs, is is unlikely that
        // this will ever escape these local minima.
        let max_isa = ISACandidate::max_isa(self.isa);
        let min_isa = self.minimum_isa_features_for_program();
        println!("{:?}", self.candidate_fitness(&min_isa));
        let mut new_generation = vec![max_isa; self.population_size / 3];
        new_generation = new_generation
            .into_iter()
            // TODO: make this a struct parameter
            .chain(vec![min_isa; 2])
            .collect();
        let mut candidate_fitnesses = vec![];

        while new_generation.len() < self.population_size {
            let candidate = self.random_isa_candidate();
            let Ok(candidate_fitness) = self.candidate_fitness(&candidate) else {
                continue;
            };

            new_generation.push(candidate);
            candidate_fitnesses.push(candidate_fitness);
        }

        let candidates = new_generation.clone();
        candidate_fitnesses = candidates
            .iter()
            .filter_map(|candidate| self.candidate_fitness(candidate).ok())
            .collect();

        self.candidates = new_generation;
        self.set_candidate_fitnesses(candidate_fitnesses);
    }

    fn minimum_isa_features_for_program(&self) -> ISACandidate {
        let mut candidate = ISACandidate::from_program(self.isa, &self.program);
        self.repair_mandatory_forms(&mut candidate);
        self.restore_unrestricted_features(&mut candidate);
        self.restore_unmutatable_fields(&mut candidate);
        println!("{:#?}", candidate.valid_field_uses);
        println!("{:#?}", candidate.active_forms);
        candidate
    }

    fn new_generation(&mut self) {
        let mut new_generation = Vec::new();
        let mut new_fitness = Vec::new();

        let candidates = self.candidates.clone();

        let top_candidate_indices: Vec<_> = self
            .candidate_fitnesses
            .iter()
            .enumerate()
            // descending sort
            .sorted_by(|(_, a), (_, b)| b.total_cmp(a))
            .take(self.elite_candidate_count)
            .map(|(idx, _)| idx)
            .collect();

        // Take the top self.elite_candidate_count candidates
        for idx in top_candidate_indices {
            new_generation.push(candidates[idx].clone());
            new_fitness.push(self.candidate_fitnesses[idx]);
        }

        let roulette_distribution =
            WeightedIndex::new(&self.candidate_fitnesses).expect("WeightedIndex not created");

        // Choose two parents to reproduce as long as we need more children
        while new_generation.len() < self.population_size {
            let remaining = self.population_size - new_generation.len();
            let mut children = Vec::with_capacity(remaining * 2);

            while children.len() < remaining * 2 {
                let parent1 = &candidates[roulette_distribution.sample(&mut self.rng)];
                let parent2 = &candidates[roulette_distribution.sample(&mut self.rng)];

                let (mut child1, mut child2) = self.reproduce(parent1, parent2);
                child1 = self.mutate(child1);
                child2 = self.mutate(child2);

                children.push(child1);
                children.push(child2);
            }

            let child_fitnesses = self.candidate_fitnesses_parallel(&children);
            for (child, fitness_result) in children.into_iter().zip(child_fitnesses) {
                if new_generation.len() == self.population_size {
                    break;
                }
                if let Ok(fitness) = fitness_result {
                    new_generation.push(child);
                    new_fitness.push(fitness);
                }
            }
        }

        // Since we generate 2 children at once, odd population sizes can overshoot by one.
        // As a result, the excess children are deemed to have unluckily died of cholera as a child.
        new_generation.truncate(self.population_size);
        new_fitness.truncate(self.population_size);

        self.candidates = new_generation;
        self.set_candidate_fitnesses(new_fitness);
    }

    fn set_candidate_fitnesses(&mut self, mut new_fitness: Vec<f64>) {
        if new_fitness.iter().all(|f| *f == 0.0) {
            new_fitness = vec![1.0; new_fitness.len()];
        }
        println!("{:?}", new_fitness);
        self.candidate_fitnesses = new_fitness;
    }

    fn candidate_fitness(&mut self, candidate: &ISACandidate) -> Result<f64, ISACandidateError> {
        let mut workspace = self.simulator.optimization_workspace();
        self.candidate_fitness_with_workspace(candidate, &mut workspace)
    }

    fn candidate_fitnesses_parallel(
        &self,
        candidates: &[ISACandidate],
    ) -> Vec<Result<f64, ISACandidateError>> {
        candidates
            .par_iter()
            .map_init(
                || self.simulator.optimization_workspace(),
                |workspace, candidate| self.candidate_fitness_with_workspace(candidate, workspace),
            )
            .collect()
    }

    fn candidate_fitness_with_workspace(
        &self,
        candidate: &ISACandidate,
        workspace: &mut OptimizationWorkspace,
    ) -> Result<f64, ISACandidateError> {
        Ok(
            self.core_area_reduction_frac_with_workspace(candidate, workspace)? * WEIGHT_CORE_SIZE
                + (1.0 - self.instruction_conflict_rate(candidate)) * WEIGHT_UNMODIFIED_PROGRAM,
        )
    }

    fn core_area_reduction_frac(
        &mut self,
        candidate: &ISACandidate,
    ) -> Result<f64, ISACandidateError> {
        let mut workspace = self.simulator.optimization_workspace();
        self.core_area_reduction_frac_with_workspace(candidate, &mut workspace)
    }

    fn core_area_reduction_frac_with_workspace(
        &self,
        candidate: &ISACandidate,
        workspace: &mut OptimizationWorkspace,
    ) -> Result<f64, ISACandidateError> {
        let total_gates = self.simulator.combinational_gate_count();
        if total_gates == 0 {
            return Ok(0.0);
        }

        Ok(
            self.gate_removal_count_with_workspace(candidate, workspace)? as f64
                / total_gates as f64,
        )
    }

    fn instruction_conflict_rate(&self, candidate: &ISACandidate) -> f64 {
        if self.program.is_empty() {
            return 0.0;
        }

        self.instruction_conflict_count(candidate) as f64 / self.program.len() as f64
    }

    fn instruction_conflict_count(&self, candidate: &ISACandidate) -> usize {
        let mut count = 0;
        for instruction in self.program.iter() {
            if !candidate.supports_instruction(instruction) {
                count += 1;
            }
        }
        count
    }

    /// Evaluates the gate count which will be able to be removed by a candidate
    fn gate_removal_count(&mut self, candidate: &ISACandidate) -> Result<usize, ISACandidateError> {
        let mut workspace = self.simulator.optimization_workspace();
        self.gate_removal_count_with_workspace(candidate, &mut workspace)
    }

    fn gate_removal_count_with_workspace(
        &self,
        candidate: &ISACandidate,
        workspace: &mut OptimizationWorkspace,
    ) -> Result<usize, ISACandidateError> {
        let valid_encodings = self.valid_encodings(candidate)?;
        let sim_inputs: Vec<_> = valid_encodings
            .iter()
            .map(|encoding| self.simulator.pattern_to_sim_inputs(encoding, "inst"))
            .collect();

        let compiled_sim_inputs = self.simulator.compile_optimization_inputs(&sim_inputs);
        let removed_gate_count = self
            .simulator
            .optimize_compiled_gate_usage_count_with_workspace(&compiled_sim_inputs, workspace);

        return Ok(removed_gate_count);
    }

    fn write_top_candidate_gatelist(&mut self, candidate: &ISACandidate) -> Result<usize, String> {
        let valid_encodings = self
            .valid_encodings(candidate)
            .map_err(|err| format!("candidate is invalid: {err:?}"))?;
        let sim_inputs: Vec<_> = valid_encodings
            .iter()
            .map(|encoding| self.simulator.pattern_to_sim_inputs(encoding, "inst"))
            .collect();

        let compiled_sim_inputs = self.simulator.compile_optimization_inputs(&sim_inputs);
        let optimization = self
            .simulator
            .optimize_compiled_gate_usage_details_with_workspace(
                &compiled_sim_inputs,
                &mut self.optimization_workspace,
            );
        let gates_to_comment = optimization.gates_to_comment.iter().cloned().collect();

        write_commented_gatelist(
            &self.netlist_file,
            TOP_CANDIDATE_GATELIST_PATH,
            &gates_to_comment,
            &optimization.assignments,
        )
        .map_err(|err| err.to_string())
    }

    /// Generate all valid encodings for an ISACandidate
    fn valid_encodings(
        &self,
        candidate: &ISACandidate,
    ) -> Result<HashSet<BitPattern>, ISACandidateError> {
        self.validate_static_instructions(candidate)?;
        self.validate_fixed_field_uses(candidate)?;

        let mut valid_encodings = HashSet::new();

        // for each instruction, collect all valid encodings
        for instr in &self.isa.instructions {
            let instruction_must_have_encoding = self.mandatory_forms.get(&instr.name).is_some();
            let mut instruction_had_encoding = false;
            for form in &instr.forms {
                let form_must_have_encoding = self
                    .mandatory_forms
                    .get(&instr.name)
                    .is_some_and(|forms| forms.contains(&form.name));

                let form_must_not_restrict_encodings = self
                    .unrestricted_forms
                    .get(&instr.name)
                    .is_some_and(|forms| forms.contains(&form.name));
                // We only want to get the encodings for the form if this form actually is used in the
                // candidate
                if !candidate
                    .active_forms
                    .get(&instr.name)
                    .is_some_and(|forms| forms.contains(&form.name))
                {
                    if form_must_not_restrict_encodings {
                        return Err(ISACandidateError::UnrestrictedFormsError);
                    }
                    if form_must_have_encoding {
                        return Err(ISACandidateError::MandatoryFormsError);
                    }
                    continue;
                }

                let encodings = form.fields_to_encodings(&candidate.valid_field_uses);
                if !encodings.is_empty() {
                    instruction_had_encoding = true;
                } else if form_must_have_encoding {
                    return Err(ISACandidateError::MandatoryFormsError);
                }

                if form_must_not_restrict_encodings {
                    let unmodified_encodings =
                        form.fields_to_encodings(&self.max_isa_candidate.valid_field_uses);
                    if Self::normalize_encoding_patterns(unmodified_encodings, instr.width)
                        != Self::normalize_encoding_patterns(encodings.clone(), instr.width)
                    {
                        return Err(ISACandidateError::UnrestrictedFormsError);
                    }
                }
                valid_encodings.extend(encodings);
            }
            if instruction_must_have_encoding && !instruction_had_encoding {
                return Err(ISACandidateError::MandatoryFormsError);
            }
        }
        Ok(valid_encodings)
    }

    fn validate_fixed_field_uses(&self, candidate: &ISACandidate) -> Result<(), ISACandidateError> {
        for (field_name, fixed_uses) in &self.fixed_field_uses {
            let Some(candidate_uses) = candidate.valid_field_uses.get(field_name) else {
                return Err(ISACandidateError::FixedFieldUsesError);
            };

            if candidate_uses.merge() != fixed_uses.merge() {
                return Err(ISACandidateError::FixedFieldUsesError);
            }
        }

        Ok(())
    }

    fn validate_static_instructions(
        &self,
        candidate: &ISACandidate,
    ) -> Result<(), ISACandidateError> {
        for instruction in self
            .program
            .iter()
            .filter(|instruction| instruction.static_instruction)
        {
            if !candidate.supports_instruction(instruction) {
                return Err(ISACandidateError::StaticInstructionError);
            }
        }
        Ok(())
    }

    fn normalize_encoding_patterns(
        encodings: Vec<BitPattern>,
        width: usize,
    ) -> HashSet<BitPattern> {
        let FieldUses::Uses { patterns, .. } = (FieldUses::Uses {
            name: "__encodings__".to_string(),
            patterns: encodings.into_iter().collect(),
            len: width,
        })
        .merge() else {
            unreachable!("normalizing encoding patterns should keep Uses merge mode");
        };
        patterns
    }

    fn repair_mandatory_forms(&self, candidate: &mut ISACandidate) {
        for instruction in &self.isa.instructions {
            let Some(mandatory_forms) = self.mandatory_forms.get(&instruction.name) else {
                continue;
            };

            if mandatory_forms.is_empty() {
                if self.instruction_has_active_encoding(candidate, instruction) {
                    continue;
                }

                let form_to_repair = instruction
                    .forms
                    .iter()
                    .find(|form| {
                        candidate
                            .active_forms
                            .get(&instruction.name)
                            .is_some_and(|forms| forms.contains(&form.name))
                    })
                    .or_else(|| instruction.forms.first());

                if let Some(form) = form_to_repair {
                    self.repair_form(candidate, &instruction.name, form);
                }
                continue;
            }

            for form_name in mandatory_forms {
                let Some(form) = instruction
                    .forms
                    .iter()
                    .find(|form| &form.name == form_name)
                else {
                    continue;
                };

                let form_has_encoding = candidate
                    .active_forms
                    .get(&instruction.name)
                    .is_some_and(|forms| forms.contains(form_name))
                    && !form
                        .fields_to_encodings(&candidate.valid_field_uses)
                        .is_empty();

                if !form_has_encoding {
                    self.repair_form(candidate, &instruction.name, form);
                }
            }
        }
    }

    fn instruction_has_active_encoding(
        &self,
        candidate: &ISACandidate,
        instruction: &crate::isa_specification::Instruction,
    ) -> bool {
        instruction.forms.iter().any(|form| {
            candidate
                .active_forms
                .get(&instruction.name)
                .is_some_and(|forms| forms.contains(&form.name))
                && !form
                    .fields_to_encodings(&candidate.valid_field_uses)
                    .is_empty()
        })
    }

    fn repair_form(
        &self,
        candidate: &mut ISACandidate,
        instruction_name: &str,
        form: &crate::isa_specification::InstructionForm,
    ) {
        candidate
            .active_forms
            .entry(instruction_name.to_string())
            .or_default()
            .insert(form.name.clone());

        for field in &form.fields {
            let Some(name) = field.name.clone() else {
                continue;
            };
            let Some(repair_value) = self.repair_value_for_field(form, field) else {
                continue;
            };
            let repair_uses = match field.merge_mode {
                MergeMode::Uses => FieldUses::Uses {
                    name: name.clone(),
                    patterns: HashSet::from([repair_value]),
                    len: field.pattern.len(),
                },
                MergeMode::VariableBits => FieldUses::VariableBits {
                    name: name.clone(),
                    pattern: Some(repair_value),
                    len: field.pattern.len(),
                },
            };

            match candidate.valid_field_uses.get_mut(&name) {
                Some(existing) => Self::merge_repair_field_use(existing, repair_uses),
                None => {
                    candidate.valid_field_uses.insert(name, repair_uses);
                }
            }
        }
    }

    fn repair_value_for_field(
        &self,
        form: &crate::isa_specification::InstructionForm,
        target_field: &crate::isa_specification::InstructionField,
    ) -> Option<BitPattern> {
        let encoding = form
            .fields_to_encodings(&self.max_isa_candidate.valid_field_uses)
            .into_iter()
            .next()?;

        let mut offset = 0;
        for field in &form.fields {
            let width = field.pattern.len();
            if std::ptr::eq(field, target_field) {
                return Some(BitPattern::new(
                    encoding.bits[offset..offset + width]
                        .iter()
                        .map(|bit| match bit {
                            Bit::Low | Bit::High => *bit,
                            Bit::Var => Bit::Low,
                            Bit::Test => {
                                panic!("repair encodings should not contain test bits")
                            }
                        })
                        .collect(),
                ));
            }
            offset += width;
        }

        None
    }

    fn merge_repair_field_use(existing: &mut FieldUses, repair: FieldUses) {
        match (existing, repair) {
            (
                FieldUses::Uses { patterns, len, .. },
                FieldUses::Uses {
                    patterns: repair_patterns,
                    len: repair_len,
                    ..
                },
            ) => {
                assert_eq!(*len, repair_len);
                patterns.extend(repair_patterns);
            }
            (
                FieldUses::VariableBits { pattern, len, .. },
                FieldUses::VariableBits {
                    pattern: Some(repair_pattern),
                    len: repair_len,
                    ..
                },
            ) => {
                assert_eq!(*len, repair_len);
                match pattern {
                    Some(existing_pattern) => {
                        for (old_bit, new_bit) in
                            existing_pattern.bits.iter_mut().zip(repair_pattern.bits)
                        {
                            if *old_bit != new_bit {
                                *old_bit = Bit::Var;
                            }
                        }
                    }
                    None => *pattern = Some(repair_pattern),
                }
            }
            _ => panic!("mandatory form repair field uses must match field merge mode"),
        }
    }

    fn unrestricted_field_names(&self) -> HashSet<FieldName> {
        self.isa
            .instructions
            .iter()
            .flat_map(|instruction| {
                instruction.forms.iter().filter_map(|form| {
                    self.unrestricted_forms
                        .get(&instruction.name)
                        .is_some_and(|forms| forms.contains(&form.name))
                        .then_some(form)
                })
            })
            .flat_map(|form| form.fields.iter())
            .filter_map(|field| field.name.clone())
            .collect()
    }

    fn restore_unrestricted_features(&self, candidate: &mut ISACandidate) {
        for field_name in self.unrestricted_field_names() {
            let Some(max_uses) = self.max_isa_candidate.valid_field_uses.get(&field_name) else {
                continue;
            };
            candidate
                .valid_field_uses
                .insert(field_name, max_uses.clone());
        }

        for (instruction_name, unrestricted_forms) in &self.unrestricted_forms {
            candidate
                .active_forms
                .entry(instruction_name.clone())
                .or_default()
                .extend(unrestricted_forms.iter().cloned());
        }
    }

    fn random_isa_candidate(&mut self) -> ISACandidate {
        let protected_fields = self.unrestricted_field_names();
        let fixed_field_uses = protected_fields
            .into_iter()
            .filter_map(|field_name| {
                self.max_isa_candidate
                    .valid_field_uses
                    .get(&field_name)
                    .cloned()
                    .map(|field_uses| (field_name, field_uses))
            })
            .collect::<HashMap<_, _>>();
        let mut candidate = ISACandidate::random_isa_with_fixed_fields(
            self.isa,
            &mut self.rng,
            &fixed_field_uses,
            &self.unrestricted_forms,
        );
        self.restore_unrestricted_features(&mut candidate);
        self.restore_unmutatable_fields(&mut candidate);
        candidate
    }

    /// Returns whether the GA may select this field as a mutable/crossover gene.
    ///
    /// Register operand selectors, such as ARM `Rn`, `Rm`, `Rd`, and `Rs`, are
    /// deliberately excluded from GA field selection when their
    /// `InstructionField` is marked `is_register_read` or `is_register_write`.
    /// Fields that occur in unrestricted forms are also excluded, since those
    /// forms must preserve their full original encoding space.
    fn field_selectable_for_ga_restriction(&self, field_name: &str) -> bool {
        let is_register_operand = self
            .isa
            .instructions
            .iter()
            .flat_map(|instruction| instruction.forms.iter())
            .flat_map(|form| form.fields.iter())
            .any(|field| {
                field.name.as_deref() == Some(field_name)
                    && (field.is_register_read || field.is_register_write)
            });

        !is_register_operand && !self.unrestricted_field_names().contains(field_name)
    }

    /// Finds fields which are not field_selectable_for_ga_restriction in a candidate, and ensures
    /// they have the maximal allowed encodings
    fn restore_unmutatable_fields(&self, candidate: &mut ISACandidate) {
        for (field_name, uses) in candidate.valid_field_uses.iter_mut() {
            if self.field_selectable_for_ga_restriction(field_name) {
                continue;
            }

            *uses = match uses {
                FieldUses::Uses { name, len, .. } => FieldUses::Uses {
                    name: name.clone(),
                    patterns: HashSet::from([BitPattern::variable(*len)]),
                    len: *len,
                },
                FieldUses::VariableBits { name, len, .. } => FieldUses::VariableBits {
                    name: name.clone(),
                    pattern: Some(BitPattern::variable(*len)),
                    len: *len,
                },
            };
        }
    }

    /// Generates children of two parents through crossover, returns two candidates
    /// Uses a uniform but granular crossover method, where there is a chance of each
    /// valid_field_uses to swap, or for the active forms of an instruction to swap
    fn reproduce(
        &mut self,
        parent1: &ISACandidate,
        parent2: &ISACandidate,
    ) -> (ISACandidate, ISACandidate) {
        let mut child1 = parent1.clone();
        let mut child2 = parent2.clone();

        if self.rng.random::<f64>() >= self.crossover_rate {
            // crossover does not occur
            return (child1, child2);
        }
        // Each parent should have the same field uses
        assert!(
            parent1.valid_field_uses.len() == parent2.valid_field_uses.len()
                && parent1
                    .valid_field_uses
                    .keys()
                    .all(|k| parent2.valid_field_uses.contains_key(k))
        );
        for key in parent1.valid_field_uses.keys() {
            if !self.field_selectable_for_ga_restriction(key) {
                continue;
            }
            if self.rng.random::<f64>() >= self.crossover_gene_rate {
                continue;
            }

            let c1_uses = child1
                .valid_field_uses
                .get_mut(key)
                .expect("valid_field_uses should contain all fields");
            let c2_uses = child2
                .valid_field_uses
                .get_mut(key)
                .expect("valid_field_uses should contain all fields");
            mem::swap(c1_uses, c2_uses);
        }

        // Now go through the active forms and potentially swap them.
        // Every instruction is expected to have an entry in active_forms.
        for instruction in self.isa.instructions.iter() {
            if self.rng.random::<f64>() >= self.crossover_gene_rate {
                continue;
            }

            let c1_forms = child1
                .active_forms
                .get_mut(&instruction.name)
                .expect("active_forms should contain all instructions");
            let c2_forms = child2
                .active_forms
                .get_mut(&instruction.name)
                .expect("active_forms should contain all instructions");
            mem::swap(c1_forms, c2_forms);
        }

        self.restore_unrestricted_features(&mut child1);
        self.restore_unrestricted_features(&mut child2);

        (child1, child2)
    }

    /// Mutates an ISA candidate
    fn mutate(&mut self, mut candidate: ISACandidate) -> ISACandidate {
        // First, mutate the fields
        let mut updates = Vec::new();
        for (field, uses) in candidate.valid_field_uses.iter() {
            if !self.field_selectable_for_ga_restriction(field) {
                continue;
            }
            if self.rng.random::<f64>() >= self.mutate_field_rate {
                continue;
            }
            let field = field.clone();
            let field_width = match uses {
                FieldUses::VariableBits { len, .. } => *len,
                FieldUses::Uses { len, .. } => *len,
            };
            let new_field = self.mutate_field(uses.clone(), field_width);
            updates.push((field, new_field));
        }

        for (field, new_field) in updates {
            candidate.valid_field_uses.insert(field, new_field);
        }

        // Then, mutate the active_forms
        for instruction in self.isa.instructions.iter() {
            if self.rng.random::<f64>() >= self.mutate_form_rate {
                continue;
            }

            let inst_name = &instruction.name;

            let active_forms = candidate
                .active_forms
                .remove(inst_name)
                .expect("All instructions should have a key in ISACandidate::active_forms");

            let new_forms = self.mutate_active_forms(inst_name, active_forms);
            candidate.active_forms.insert(inst_name.clone(), new_forms);
        }

        self.restore_unrestricted_features(&mut candidate);

        candidate
    }

    /// Generates a new, completely random active_forms
    fn mutate_active_forms(
        &mut self,
        instruction_name: &str,
        _active_forms: HashSet<String>,
    ) -> HashSet<String> {
        // Either add or remove an active form, proportional to the total number of forms
        let instruction = self
            .isa
            .instructions
            .iter()
            .find(|i| i.name == instruction_name)
            .expect("instruction_name must be a valid instruction in the ISA");
        let num_forms = instruction.forms.len();
        let unrestricted_forms = self
            .unrestricted_forms
            .get(instruction_name)
            .cloned()
            .unwrap_or_default();

        let forms = &instruction.forms;
        let unrestricted_forms_in_instr: Vec<_> = forms
            .iter()
            .filter(|f| unrestricted_forms.contains(&f.name))
            .collect();

        let non_unrestricted_forms_in_instr: Vec<_> = forms
            .iter()
            .filter(|f| !unrestricted_forms.contains(&f.name))
            .collect();

        let num_forms_to_include = self
            .rng
            .random_range(0..=(num_forms - unrestricted_forms_in_instr.len()));

        let new_forms = unrestricted_forms_in_instr
            .into_iter()
            .chain(
                non_unrestricted_forms_in_instr
                    .into_iter()
                    .sample(&mut self.rng, num_forms_to_include),
            )
            .map(|f| f.name.clone())
            .collect();

        new_forms

        // let num_active_forms = active_forms.len();
        // let removable_forms = active_forms
        //     .difference(&unrestricted_forms)
        //     .cloned()
        //     .collect::<Vec<_>>();

        // // Create a sampling distribution to decide whether to remove an existing form, or add a new one
        // let mut freqs = vec![1; removable_forms.len()];
        // freqs.push(num_forms - num_active_forms);

        // if freqs.iter().all(|freq| *freq == 0) {
        //     return active_forms;
        // }

        // let dist = WeightedIndex::new(&freqs).expect("WeightedIndex not created");
        // let form_idx = dist.sample(&mut self.rng);

        // if form_idx == removable_forms.len() {
        //     // Find a form in `instruction` that isn't used
        //     let unused_forms = instruction
        //         .forms
        //         .iter()
        //         .filter(|f| !active_forms.contains(&f.name));
        //     active_forms.insert(
        //         unused_forms
        //             .choose(&mut self.rng)
        //             .expect("There should be at least one unused form!")
        //             .name
        //             .clone(),
        //     );
        // } else {
        //     // Choose a random form to remove
        //     let form_to_remove = removable_forms[form_idx].clone();
        //     active_forms.remove(&form_to_remove);
        // }

        // active_forms
    }

    /// Mutates the provided field
    fn mutate_field(&mut self, field: FieldUses, field_width: usize) -> FieldUses {
        match field {
            FieldUses::VariableBits { name, pattern, len } => {
                assert_eq!(
                    len, field_width,
                    "FieldUses::VariableBits len must match field_width"
                );
                let Some(mut pattern) = pattern else {
                    return FieldUses::VariableBits {
                        name,
                        pattern: Some(ISACandidate::random_bit_pattern(field_width, &mut self.rng)),
                        len,
                    };
                };
                if self.rng.random::<f64>() < P_MUT_VAR_TO_NONE {
                    return FieldUses::VariableBits {
                        name,
                        pattern: None,
                        len,
                    };
                }
                // Choose a random bit to flip
                let bit_idx = self.rng.random_range(0..pattern.bits.len());

                // We also want to have a chance of either flipping the bit or making it more
                // permissive
                // ie Bit::Low should either go to Bit::High or Bit::Var
                let const_to_var = self.rng.random::<f64>() > P_MUT_CONST_TO_VAR;
                let new_bit = if const_to_var {
                    match pattern.bits[bit_idx] {
                        Bit::Low | Bit::High => Bit::Var,
                        // If variable, we choose a random bit
                        _ => choose_random_bit(&mut self.rng),
                    }
                } else {
                    match pattern.bits[bit_idx] {
                        Bit::Low => Bit::High,
                        Bit::High => Bit::Low,
                        // If variable, we choose a random bit
                        _ => choose_random_bit(&mut self.rng),
                    }
                };
                pattern.bits[bit_idx] = new_bit;
                FieldUses::VariableBits {
                    name,
                    pattern: Some(pattern),
                    len,
                }
            }

            FieldUses::Uses {
                name,
                mut patterns,
                len,
            } => {
                assert_eq!(
                    len, field_width,
                    "FieldUses::Uses len must match field_width"
                );
                assert!(
                    patterns.iter().all(|pattern| pattern.len() == len),
                    "All FieldUses::Uses patterns must match len"
                );
                // For `Uses`, what is done is constructing a weighted average.
                // Each pattern has a frequncy of 2^k where k = number of variable bits, and there
                // is finally a frequency for non-included patterns, equal to the number of patterns
                // that are uncovered
                //
                // One of these patterns is selected according to this weighting. If a pattern is
                // selected, a random variable bit is chosen to switch to a non-variable bit. Or, if
                // there are no variable bits in a pattern, that pattern is removed.
                // If the non-included patterns are selected, a random sequence of high and low bits
                // which isn't covered by the current set of Bifield_length: usizetPatterns is
                // selected.

                let mut patterns_ordered = patterns.clone().into_iter().collect();
                let mut freqs = Self::construct_bitpatterns_frequencies(&patterns_ordered);

                let uncovered = Self::uncovered_patterns(&patterns, field_width);

                // Now we give a frequency in the distribution for the number of uncovered bit patterns
                freqs.push(
                    uncovered
                        .iter()
                        .map(|p| 1 << p.num_variable())
                        .sum::<u128>(),
                );
                let dist = WeightedIndex::new(&freqs).expect("WeightedIndex not created");
                let pattern_idx = dist.sample(&mut self.rng);

                // This doesn't correspond with a real pattern, it means we want to add a random
                // uncovered pattern
                if pattern_idx == patterns_ordered.len() {
                    patterns.insert(self.random_pattern(&uncovered, field_width));
                } else {
                    // Now, take the pattern out of `patterns`, flip a variable bit to a
                    // non-variable, and add it back
                    let pattern = patterns_ordered.remove(pattern_idx);
                    patterns.remove(&pattern);
                    if pattern.num_variable() != 0 {
                        let point = BitPattern {
                            bits: pattern
                                .bits
                                .iter()
                                .map(|bit| {
                                    if *bit == Bit::Var {
                                        *[Bit::Low, Bit::High]
                                            .choose(&mut self.rng)
                                            .expect("Array has 2 elements")
                                    } else {
                                        *bit
                                    }
                                })
                                .collect(),
                        };
                        patterns.extend(pattern.cube_subtract(&point));
                    }
                }
                FieldUses::Uses {
                    name,
                    patterns,
                    len,
                }
                .merge()
            }
        }
    }

    fn uncovered_patterns(
        patterns: &HashSet<BitPattern>,
        field_width: usize,
    ) -> HashSet<BitPattern> {
        assert!(
            patterns.iter().all(|pattern| pattern.len() == field_width),
            "All patterns must match field_width"
        );
        let universal = BitPattern::variable(field_width);
        let mut uncovered_patterns = HashSet::from([universal]);

        for pattern in patterns {
            let mut new_uncovered = HashSet::new();
            for uncovered in uncovered_patterns.iter() {
                new_uncovered.extend(uncovered.cube_subtract(pattern));
            }
            uncovered_patterns = new_uncovered;
        }
        uncovered_patterns
    }

    fn random_pattern(&mut self, patterns: &HashSet<BitPattern>, field_width: usize) -> BitPattern {
        assert!(
            patterns.iter().all(|pattern| pattern.len() == field_width),
            "All patterns must match field_width"
        );

        let mut patterns_ordered = patterns.into_iter().cloned().collect();
        let weights = Self::construct_bitpatterns_frequencies(&patterns_ordered);

        let dist = WeightedIndex::new(&weights).expect("WeightedIndex not created");
        let mut pattern = patterns_ordered.remove(dist.sample(&mut self.rng));

        for bit in &mut pattern.bits {
            if *bit == Bit::Var {
                *bit = if self.rng.random() {
                    Bit::High
                } else {
                    Bit::Low
                };
            }
        }

        pattern
    }

    fn construct_bitpatterns_frequencies(patterns: &Vec<BitPattern>) -> Vec<u128> {
        let mut freqs = vec![0; patterns.len()];
        for (idx, pattern) in patterns.iter().enumerate() {
            freqs[idx] = 1 << pattern.num_variable();
        }
        freqs
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ISACandidateError {
    MandatoryFormsError,
    UnrestrictedFormsError,
    FixedFieldUsesError,
    StaticInstructionError,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ISACandidate {
    pub valid_field_uses: HashMap<FieldName, FieldUses>,
    /// Key: instruction name. Value: set of form names
    pub active_forms: HashMap<String, HashSet<String>>,
}

impl ISACandidate {
    pub fn supports_instruction(&self, instruction: &DecodedInstruction) -> bool {
        self.active_forms
            .get(&instruction.name)
            .is_some_and(|forms| forms.contains(&instruction.form.name))
            && instruction_valid_under_field_uses(instruction, &self.valid_field_uses)
    }

    pub fn from_program(isa: &ISA, program: &[DecodedInstruction]) -> Self {
        let mut observed_field_uses = HashMap::new();
        let mut active_forms = isa
            .instructions
            .iter()
            .map(|instruction| (instruction.name.clone(), HashSet::new()))
            .collect::<HashMap<_, _>>();

        for decoded in program {
            active_forms
                .entry(decoded.name.clone())
                .or_default()
                .insert(decoded.form.name.clone());

            for field in &decoded.fields {
                let Some(name) = field.name.clone() else {
                    continue;
                };
                let default_val = match field.merge_mode {
                    MergeMode::Uses => FieldUses::Uses {
                        name: name.clone(),
                        patterns: HashSet::from([field.value.clone()]),
                        len: field.value.len(),
                    },
                    MergeMode::VariableBits => FieldUses::VariableBits {
                        name: name.clone(),
                        pattern: Some(field.value.clone()),
                        len: field.value.len(),
                    },
                };

                match observed_field_uses
                    .entry(name.clone())
                    .or_insert(default_val)
                {
                    FieldUses::Uses { patterns, len, .. } => {
                        assert_eq!(
                            *len,
                            field.value.len(),
                            "Pattern length mismatch for field '{}'",
                            name
                        );
                        patterns.insert(field.value.clone());
                    }
                    FieldUses::VariableBits { pattern, len, .. } => {
                        assert_eq!(
                            *len,
                            field.value.len(),
                            "Pattern length mismatch for field '{}'",
                            name
                        );
                        let pattern = pattern
                            .as_mut()
                            .expect("observed VariableBits should contain a pattern");
                        for (old_bit, new_bit) in pattern.bits.iter_mut().zip(&field.value.bits) {
                            if *old_bit != *new_bit {
                                *old_bit = Bit::Var;
                            }
                        }
                    }
                }
            }
        }

        let observed_field_uses = observed_field_uses
            .into_iter()
            .map(|(name, field_uses)| (name, field_uses.merge()))
            .collect::<HashMap<_, _>>();
        let mut valid_field_uses = Self::empty_isa_field_uses(isa);
        valid_field_uses.extend(observed_field_uses);

        Self {
            valid_field_uses,
            active_forms,
        }
    }

    /// Generates an ISACandidate which supports all functions of an ISA
    pub fn max_isa(isa: &ISA) -> Self {
        let mut valid_field_uses = HashMap::new();
        let mut active_forms = HashMap::new();
        for instruction in isa.instructions.iter() {
            active_forms.insert(instruction.name.clone(), HashSet::new());
            let instr_forms = active_forms
                .get_mut(&instruction.name)
                .expect("Just added item to hashmap, but it isn't there!");
            for form in instruction.forms.iter() {
                instr_forms.insert(form.name.clone());
                for field in form.fields.iter() {
                    let Some(name) = field.name.clone() else {
                        continue;
                    };
                    if valid_field_uses.contains_key(&name) {
                        continue;
                    }
                    match field.merge_mode {
                        MergeMode::Uses => {
                            valid_field_uses.insert(
                                name.clone(),
                                FieldUses::Uses {
                                    name,
                                    patterns: HashSet::from([field.pattern.clone()]),
                                    len: field.pattern.len(),
                                },
                            );
                        }
                        MergeMode::VariableBits => {
                            valid_field_uses.insert(
                                name.clone(),
                                FieldUses::VariableBits {
                                    name,
                                    pattern: Some(field.pattern.clone()),
                                    len: field.pattern.len(),
                                },
                            );
                        }
                    }
                }
            }
        }
        Self {
            valid_field_uses,
            active_forms,
        }
    }

    /// Generates a random ISACandidate with the same field names, field widths, and instruction
    /// keys as the ISA.
    pub fn random_isa<R: Rng>(isa: &ISA, rng: &mut R) -> Self {
        Self::random_isa_with_fixed_fields(isa, rng, &HashMap::new(), &HashMap::new())
    }

    fn random_isa_with_fixed_fields<R: Rng>(
        isa: &ISA,
        rng: &mut R,
        fixed_field_uses: &HashMap<FieldName, FieldUses>,
        required_active_forms: &HashMap<String, HashSet<String>>,
    ) -> Self {
        let mut valid_field_uses = HashMap::new();
        let mut active_forms = HashMap::new();

        for instruction in isa.instructions.iter() {
            active_forms.insert(instruction.name.clone(), HashSet::new());
            let instr_forms = active_forms
                .get_mut(&instruction.name)
                .expect("Just added item to hashmap, but it isn't there!");

            for form in instruction.forms.iter() {
                if rng.random()
                    || required_active_forms
                        .get(&instruction.name)
                        .is_some_and(|forms| forms.contains(&form.name))
                {
                    instr_forms.insert(form.name.clone());
                }

                for field in form.fields.iter() {
                    let Some(name) = field.name.clone() else {
                        continue;
                    };
                    if valid_field_uses.contains_key(&name) {
                        continue;
                    }

                    let field_uses = fixed_field_uses
                        .get(&name)
                        .cloned()
                        .unwrap_or_else(|| Self::random_field_use(field, rng));
                    valid_field_uses.insert(name.clone(), field_uses);
                }
            }
        }

        Self {
            valid_field_uses,
            active_forms,
        }
    }

    fn random_field_use<R: Rng>(
        field: &crate::isa_specification::InstructionField,
        rng: &mut R,
    ) -> FieldUses {
        let name = field
            .name
            .clone()
            .expect("random_field_use requires a named field");
        let len = field.pattern.len();
        match field.merge_mode {
            // Generate at least one concrete pattern so the initial random ISA is not
            // trivially empty for every form using this field.
            MergeMode::Uses => FieldUses::Uses {
                name,
                patterns: (0..rng.random_range(1..=(1 << len)))
                    .map(|_| Self::random_concrete_pattern(len, rng))
                    .collect(),
                len,
            }
            .merge(),
            MergeMode::VariableBits => FieldUses::VariableBits {
                name,
                pattern: Some(Self::random_bit_pattern(len, rng)),
                len,
            },
        }
    }

    fn empty_isa_field_uses(isa: &ISA) -> HashMap<FieldName, FieldUses> {
        let mut valid_field_uses = HashMap::new();
        for instruction in isa.instructions.iter() {
            for form in instruction.forms.iter() {
                for field in form.fields.iter() {
                    let Some(name) = field.name.clone() else {
                        continue;
                    };
                    if valid_field_uses.contains_key(&name) {
                        continue;
                    }
                    match field.merge_mode {
                        MergeMode::Uses => {
                            valid_field_uses.insert(
                                name.clone(),
                                FieldUses::Uses {
                                    name,
                                    patterns: HashSet::new(),
                                    len: field.pattern.len(),
                                },
                            );
                        }
                        MergeMode::VariableBits => {
                            valid_field_uses.insert(
                                name.clone(),
                                FieldUses::VariableBits {
                                    name,
                                    pattern: None,
                                    len: field.pattern.len(),
                                },
                            );
                        }
                    }
                }
            }
        }
        valid_field_uses
    }

    fn random_bit_pattern<R: Rng>(len: usize, rng: &mut R) -> BitPattern {
        BitPattern {
            bits: (0..len)
                .map(|_| match rng.random_range(0..3) {
                    0 => Bit::Low,
                    1 => Bit::High,
                    _ => Bit::Var,
                })
                .collect(),
        }
    }

    fn random_concrete_pattern<R: Rng>(len: usize, rng: &mut R) -> BitPattern {
        BitPattern {
            bits: (0..len).map(|_| choose_random_bit(rng)).collect(),
        }
    }
}

fn choose_random_bit<R: Rng>(rng: &mut R) -> Bit {
    let bit = rng.random_range(0..=1);
    if bit == 0 {
        Bit::Low
    } else {
        Bit::High
    }
}

fn instance_name_on_line(line: &str) -> Option<&str> {
    let before_connections = line.split_once('(')?.0.trim_end();
    let mut tokens = before_connections.split_whitespace();
    tokens.next()?;
    tokens.last()
}

fn bit_to_verilog_const(bit: Bit) -> &'static str {
    match bit {
        Bit::Low => "1'b0",
        Bit::High => "1'b1",
        Bit::Var | Bit::Test => panic!("Cannot assign non-constant bit {:?}", bit),
    }
}

/// Writes a copy of `source_path` with unused gate instances commented out and
/// constant output assignments inserted before `endmodule`.
///
/// # Errors
///
/// Returns any I/O error from reading the source netlist, creating the output
/// directory, or writing the output netlist.
pub fn write_commented_gatelist(
    source_path: &str,
    output_path: &str,
    gates_to_comment: &HashSet<String>,
    assignments: &[GateOutputAssignment],
) -> std::io::Result<usize> {
    let verilog = fs::read_to_string(source_path)?;
    let mut commented_gate_count = 0;
    let mut comment_current_instance = false;
    let mut optimized_lines = Vec::new();

    for line in verilog.lines() {
        let starts_unused_instance = !comment_current_instance
            && instance_name_on_line(line).is_some_and(|name| gates_to_comment.contains(name));

        let should_comment = comment_current_instance || starts_unused_instance;
        if should_comment {
            optimized_lines.push(format!("//{line}"));

            if starts_unused_instance {
                commented_gate_count += 1;
            }

            comment_current_instance = !line.trim_end().ends_with(';');
        } else {
            optimized_lines.push(line.to_string());
        }
    }

    let assign_statements = assignments
        .iter()
        .map(|assignment| {
            format!(
                "  assign {} = {};",
                assignment.wire_name,
                bit_to_verilog_const(assignment.value)
            )
        })
        .collect::<Vec<_>>();

    if !assign_statements.is_empty() {
        let endmodule_idx = optimized_lines
            .iter()
            .rposition(|line| line.trim() == "endmodule")
            .expect("commented gatelist should contain endmodule");
        optimized_lines.splice(endmodule_idx..endmodule_idx, assign_statements);
    }

    let mut optimized_verilog = optimized_lines.join("\n");
    optimized_verilog.push('\n');

    if let Some(parent) = Path::new(output_path).parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(output_path, optimized_verilog)?;

    Ok(commented_gate_count)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isa_specification::{
        ArchitecturalRegister, Instruction, InstructionField, InstructionForm, StackDirection,
        StackPointer,
    };
    use rand::{rngs::StdRng, SeedableRng};
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicUsize, Ordering},
    };

    static TEST_FILE_COUNTER: AtomicUsize = AtomicUsize::new(0);

    fn write_temp_file(prefix: &str, contents: &str) -> String {
        let id = TEST_FILE_COUNTER.fetch_add(1, Ordering::Relaxed);
        let mut path: PathBuf = std::env::temp_dir();
        path.push(format!(
            "isa_minimization_isa_optimization_{}_{}_{}.v",
            prefix,
            std::process::id(),
            id
        ));
        fs::write(&path, contents).unwrap();
        path.to_string_lossy().into_owned()
    }

    fn test_netlist_path() -> String {
        let verilog = r#"
            module top(input [1:0] inst, output y);
                BUF_X1 g_buf(.A (inst[0]), .Z (y));
            endmodule
        "#;
        write_temp_file("netlist", verilog)
    }

    fn test_isa() -> ISA {
        let register = ArchitecturalRegister {
            identifier: 0,
            identifier_width: 1,
            width: 1,
        };

        ISA {
            registers: vec![register],
            instructions: vec![],
            sp: StackPointer {
                register,
                stack_size: 0,
                direction: StackDirection::Downwards,
            },
            pc: register,
        }
    }

    fn isa_with_instructions(instructions: Vec<Instruction>) -> ISA {
        ISA {
            instructions,
            ..test_isa()
        }
    }

    fn one_field_instruction() -> Instruction {
        Instruction::new("INST", 2).form(
            InstructionForm::new("base")
                .field(InstructionField::constant("1"))
                .field(InstructionField::variable("bit", 1)),
        )
    }

    fn two_form_instruction() -> Instruction {
        Instruction::new("INST", 2)
            .form(
                InstructionForm::new("base")
                    .field(InstructionField::constant("1"))
                    .field(InstructionField::variable("bit", 1)),
            )
            .form(
                InstructionForm::new("inactive")
                    .field(InstructionField::constant("0"))
                    .field(InstructionField::variable("bit", 1)),
            )
    }

    fn uses_field_instruction() -> Instruction {
        Instruction::new("USES", 3).form(
            InstructionForm::new("base")
                .field(InstructionField::constant("1"))
                .field(InstructionField::variable("opcode", 2).merge_mode_uses()),
        )
    }

    fn two_uses_field_instruction() -> Instruction {
        Instruction::new("USES2", 5).form(
            InstructionForm::new("base")
                .field(InstructionField::constant("1"))
                .field(InstructionField::variable("left", 2).merge_mode_uses())
                .field(InstructionField::variable("right", 2).merge_mode_uses()),
        )
    }

    fn unrestricted_field_instruction() -> Instruction {
        Instruction::new("UNRES", 3)
            .form(
                InstructionForm::new("base")
                    .field(InstructionField::constant("1"))
                    .field(InstructionField::variable("opcode", 2).merge_mode_uses()),
            )
            .form(
                InstructionForm::new("inactive")
                    .field(InstructionField::constant("0"))
                    .field(InstructionField::variable("mode", 2)),
            )
    }

    fn register_operand_instruction() -> Instruction {
        Instruction::new("REG", 4).form(
            InstructionForm::new("base")
                .field(InstructionField::constant("1"))
                .field(
                    InstructionField::variable("rn", 2)
                        .merge_mode_uses()
                        .register_read(),
                )
                .field(InstructionField::variable("mode", 1)),
        )
    }

    fn decode_one(isa: &ISA, bits: &str) -> DecodedInstruction {
        let decoded =
            DecodedInstruction::decode_program_str(bits, isa).expect("test instruction decodes");
        assert_eq!(decoded.len(), 1);
        decoded.into_iter().next().unwrap()
    }

    fn static_decode_one(isa: &ISA, bits: &str) -> DecodedInstruction {
        let mut decoded = decode_one(isa, bits);
        decoded.static_instruction = true;
        decoded
    }

    fn manager(rng: StdRng) -> IsaOptimizationManager<'static, StdRng> {
        let isa = Box::leak(Box::new(test_isa()));
        let netlist_path = test_netlist_path();
        IsaOptimizationManager::new(
            isa,
            rng,
            HashMap::new(),
            HashMap::new(),
            &netlist_path,
            "examples/NangateOpenCellLibrary_typical.lib",
            vec![],
            1,
            0,
            0.0,
            0.0,
            1.0,
            0.0,
        )
    }

    fn manager_with(
        isa: ISA,
        rng: StdRng,
        mandatory_forms: HashMap<String, HashSet<String>>,
        program: Vec<DecodedInstruction>,
    ) -> IsaOptimizationManager<'static, StdRng> {
        manager_with_forms(isa, rng, mandatory_forms, HashMap::new(), program)
    }

    fn manager_with_forms(
        isa: ISA,
        rng: StdRng,
        mandatory_forms: HashMap<String, HashSet<String>>,
        unrestricted_forms: HashMap<String, HashSet<String>>,
        program: Vec<DecodedInstruction>,
    ) -> IsaOptimizationManager<'static, StdRng> {
        let isa = Box::leak(Box::new(isa));
        let netlist_path = test_netlist_path();
        IsaOptimizationManager::new(
            isa,
            rng,
            mandatory_forms,
            unrestricted_forms,
            &netlist_path,
            "examples/NangateOpenCellLibrary_typical.lib",
            program,
            1,
            0,
            0.0,
            0.0,
            1.0,
            0.0,
        )
    }

    fn patterns(patterns: &[&str]) -> HashSet<BitPattern> {
        patterns
            .iter()
            .map(|pattern| BitPattern::parse(pattern))
            .collect()
    }

    fn pattern_string(pattern: &BitPattern) -> String {
        pattern
            .bits
            .iter()
            .map(|bit| match bit {
                Bit::Low => '0',
                Bit::High => '1',
                Bit::Var => 'x',
                Bit::Test => 't',
            })
            .collect()
    }

    fn assert_concrete(pattern: &BitPattern) {
        assert!(
            pattern
                .bits
                .iter()
                .all(|bit| matches!(bit, Bit::Low | Bit::High)),
            "expected a concrete pattern, got {}",
            pattern_string(pattern)
        );
    }

    fn assert_uncovered(pattern: &BitPattern, covered: &HashSet<BitPattern>) {
        assert!(
            !covered
                .iter()
                .any(|covered_pattern| covered_pattern.matches_bits(&pattern.bits)),
            "expected {} to be uncovered",
            pattern_string(pattern)
        );
    }

    fn variable_bits_field(pattern: &str) -> FieldUses {
        FieldUses::VariableBits {
            name: "field".to_string(),
            pattern: Some(BitPattern::parse(pattern)),
            len: pattern.len(),
        }
    }

    fn empty_variable_bits_field(len: usize) -> FieldUses {
        FieldUses::VariableBits {
            name: "field".to_string(),
            pattern: None,
            len,
        }
    }

    fn uses_field(patterns: &[&str]) -> FieldUses {
        let len = patterns
            .first()
            .map(|pattern| pattern.len())
            .expect("Uses test helper requires at least one pattern");
        assert!(
            patterns.iter().all(|pattern| pattern.len() == len),
            "Uses test helper patterns must have the same length"
        );
        FieldUses::Uses {
            name: "field".to_string(),
            patterns: self::patterns(patterns),
            len,
        }
    }

    fn unwrap_variable_bits(field: FieldUses) -> BitPattern {
        let FieldUses::VariableBits { pattern, .. } = field else {
            panic!("expected VariableBits field");
        };
        pattern.expect("expected populated VariableBits pattern")
    }

    fn unwrap_uses(field: FieldUses) -> HashSet<BitPattern> {
        let FieldUses::Uses { patterns, .. } = field else {
            panic!("expected Uses field");
        };
        patterns
    }

    fn candidate(fields: &[(&str, FieldUses)]) -> ISACandidate {
        ISACandidate {
            valid_field_uses: fields
                .iter()
                .map(|(name, field)| (name.to_string(), field.clone()))
                .collect(),
            active_forms: HashMap::new(),
        }
    }

    fn candidate_with_active_forms(
        fields: &[(&str, FieldUses)],
        active_forms: &[(&str, &[&str])],
    ) -> ISACandidate {
        ISACandidate {
            valid_field_uses: fields
                .iter()
                .map(|(name, field)| (name.to_string(), field.clone()))
                .collect(),
            active_forms: active_forms
                .iter()
                .map(|(instruction, forms)| {
                    (
                        instruction.to_string(),
                        forms.iter().map(|form| form.to_string()).collect(),
                    )
                })
                .collect(),
        }
    }

    fn valid_encodings_ok(
        manager: &IsaOptimizationManager<'_, StdRng>,
        candidate: &ISACandidate,
    ) -> HashSet<BitPattern> {
        match manager.valid_encodings(candidate) {
            Ok(encodings) => encodings,
            Err(ISACandidateError::MandatoryFormsError) => {
                panic!("valid_encodings unexpectedly rejected mandatory forms")
            }
            Err(ISACandidateError::UnrestrictedFormsError) => {
                panic!("valid_encodings unexpectedly rejected unrestricted forms")
            }
            Err(ISACandidateError::FixedFieldUsesError) => {
                panic!("valid_encodings unexpectedly rejected fixed field uses")
            }
            Err(ISACandidateError::StaticInstructionError) => {
                panic!("valid_encodings unexpectedly rejected static instructions")
            }
        }
    }

    fn assert_same_field_use_shape(left: &ISACandidate, right: &ISACandidate) {
        assert_eq!(
            left.valid_field_uses.keys().collect::<HashSet<_>>(),
            right.valid_field_uses.keys().collect::<HashSet<_>>()
        );

        for (name, left_field) in &left.valid_field_uses {
            let right_field = right
                .valid_field_uses
                .get(name)
                .expect("field key sets should match");
            match (left_field, right_field) {
                (
                    FieldUses::VariableBits { len: left_len, .. },
                    FieldUses::VariableBits { len: right_len, .. },
                ) => assert_eq!(left_len, right_len),
                (FieldUses::Uses { len: left_len, .. }, FieldUses::Uses { len: right_len, .. }) => {
                    assert_eq!(left_len, right_len)
                }
                _ => panic!("field {name} has different FieldUses variants"),
            }
        }
    }

    #[test]
    fn random_isa_preserves_instruction_keys_field_modes_and_widths() {
        let isa = isa_with_instructions(vec![Instruction::new("INST", 4).form(
            InstructionForm::new("base")
                .field(InstructionField::variable("var", 2))
                .field(InstructionField::variable("uses", 2).merge_mode_uses()),
        )]);
        let mut rng = StdRng::seed_from_u64(0x5100);

        let candidate = ISACandidate::random_isa(&isa, &mut rng);

        assert!(candidate.active_forms.contains_key("INST"));
        assert_eq!(candidate.valid_field_uses.len(), 2);

        let FieldUses::VariableBits { pattern, .. } = candidate
            .valid_field_uses
            .get("var")
            .expect("var field should be present")
        else {
            panic!("expected VariableBits field");
        };
        assert_eq!(
            pattern
                .as_ref()
                .expect("random ISA should populate var")
                .len(),
            2
        );

        let FieldUses::Uses { patterns, len, .. } = candidate
            .valid_field_uses
            .get("uses")
            .expect("uses field should be present")
        else {
            panic!("expected Uses field");
        };
        assert_eq!(*len, 2);
        assert_eq!(patterns.len(), 1);
        assert!(patterns.iter().all(|pattern| pattern.len() == *len));
        assert!(patterns.iter().all(|pattern| {
            pattern
                .bits
                .iter()
                .all(|bit| matches!(bit, Bit::Low | Bit::High))
        }));
    }

    #[test]
    fn random_isa_is_deterministic_for_seeded_rng() {
        let isa = isa_with_instructions(vec![two_form_instruction()]);
        let mut rng1 = StdRng::seed_from_u64(0x5101);
        let mut rng2 = StdRng::seed_from_u64(0x5101);

        assert_eq!(
            ISACandidate::random_isa(&isa, &mut rng1),
            ISACandidate::random_isa(&isa, &mut rng2)
        );
    }

    #[test]
    fn from_program_builds_minimum_field_uses_and_active_forms() {
        let isa = isa_with_instructions(vec![
            Instruction::new("INST", 4)
                .form(
                    InstructionForm::new("base")
                        .field(InstructionField::constant("10"))
                        .field(InstructionField::variable("mode", 1))
                        .field(InstructionField::variable("opcode", 1).merge_mode_uses()),
                )
                .form(
                    InstructionForm::new("other")
                        .field(InstructionField::constant("11"))
                        .field(InstructionField::variable("mode", 1))
                        .field(InstructionField::variable("opcode", 1).merge_mode_uses()),
                ),
            Instruction::new("UNUSED", 3).form(
                InstructionForm::new("base")
                    .field(InstructionField::constant("0"))
                    .field(InstructionField::variable("unused", 2)),
            ),
        ]);
        let program = vec![decode_one(&isa, "1000"), decode_one(&isa, "1011")];

        let candidate = ISACandidate::from_program(&isa, &program);

        assert_eq!(
            candidate.active_forms.get("INST"),
            Some(&HashSet::from(["base".to_string()]))
        );
        assert_eq!(candidate.active_forms.get("UNUSED"), Some(&HashSet::new()));
        assert_eq!(candidate.valid_field_uses.len(), 3);
        assert_eq!(
            candidate.valid_field_uses.get("mode"),
            Some(&FieldUses::VariableBits {
                name: "mode".to_string(),
                pattern: Some(BitPattern::parse("x")),
                len: 1,
            })
        );
        assert_eq!(
            candidate.valid_field_uses.get("opcode"),
            Some(&FieldUses::Uses {
                name: "opcode".to_string(),
                patterns: patterns(&["x"]),
                len: 1,
            })
        );
        assert_eq!(
            candidate.valid_field_uses.get("unused"),
            Some(&FieldUses::VariableBits {
                name: "unused".to_string(),
                pattern: None,
                len: 2,
            })
        );
    }

    #[test]
    fn minimum_isa_repairs_missing_explicit_mandatory_form() {
        let isa = isa_with_instructions(vec![
            Instruction::new("USED", 2).form(
                InstructionForm::new("base")
                    .field(InstructionField::constant("1"))
                    .field(InstructionField::variable("bit", 1)),
            ),
            Instruction::new("MAND", 3).form(
                InstructionForm::new("base")
                    .field(InstructionField::constant("0"))
                    .field(InstructionField::variable("opcode", 2).merge_mode_uses()),
            ),
            Instruction::new("OPTIONAL", 2).form(
                InstructionForm::new("base")
                    .field(InstructionField::constant("0"))
                    .field(InstructionField::variable("unused", 1)),
            ),
        ]);
        let program = vec![decode_one(&isa, "11")];
        let mandatory_forms =
            HashMap::from([("MAND".to_string(), HashSet::from(["base".to_string()]))]);
        let manager = manager_with(isa, StdRng::seed_from_u64(0x510B), mandatory_forms, program);

        let candidate = manager.minimum_isa_features_for_program();

        assert_eq!(
            candidate.active_forms.get("MAND"),
            Some(&HashSet::from(["base".to_string()]))
        );
        assert_eq!(
            candidate.active_forms.get("OPTIONAL"),
            Some(&HashSet::new())
        );
        let FieldUses::Uses { patterns, .. } = candidate
            .valid_field_uses
            .get("opcode")
            .expect("mandatory repair should add opcode")
        else {
            panic!("expected Uses field");
        };
        assert_eq!(patterns.len(), 1);
        assert!(patterns.iter().all(|pattern| {
            pattern
                .bits
                .iter()
                .all(|bit| matches!(bit, Bit::Low | Bit::High))
        }));
        assert!(matches!(manager.valid_encodings(&candidate), Ok(_)));
    }

    #[test]
    fn minimum_isa_mandatory_repair_merges_with_program_fields() {
        let isa = isa_with_instructions(vec![Instruction::new("INST", 2)
            .form(
                InstructionForm::new("program")
                    .field(InstructionField::constant("1"))
                    .field(InstructionField::variable("mode", 1)),
            )
            .form(
                InstructionForm::new("mandatory")
                    .field(InstructionField::constant("0"))
                    .field(InstructionField::variable("mode", 1)),
            )]);
        let program = vec![decode_one(&isa, "11")];
        let mandatory_forms =
            HashMap::from([("INST".to_string(), HashSet::from(["mandatory".to_string()]))]);
        let manager = manager_with(isa, StdRng::seed_from_u64(0x510D), mandatory_forms, program);

        let candidate = manager.minimum_isa_features_for_program();

        assert_eq!(
            candidate.valid_field_uses.get("mode"),
            Some(&FieldUses::VariableBits {
                name: "mode".to_string(),
                pattern: Some(BitPattern::parse("x")),
                len: 1,
            })
        );
        assert!(matches!(manager.valid_encodings(&candidate), Ok(_)));
    }

    #[test]
    fn minimum_isa_repairs_empty_mandatory_instruction_with_one_form() {
        let isa = isa_with_instructions(vec![two_form_instruction()]);
        let mandatory_forms = HashMap::from([("INST".to_string(), HashSet::new())]);
        let manager = manager_with(isa, StdRng::seed_from_u64(0x510C), mandatory_forms, vec![]);

        let candidate = manager.minimum_isa_features_for_program();
        let active_forms = candidate
            .active_forms
            .get("INST")
            .expect("candidate should have an INST active-form entry");

        assert_eq!(active_forms.len(), 1);
        assert!(active_forms.contains("base") || active_forms.contains("inactive"));
        assert!(matches!(manager.valid_encodings(&candidate), Ok(_)));
    }

    #[test]
    fn all_isa_candidate_constructors_create_compatible_valid_field_uses() {
        let isa = isa_with_instructions(vec![
            Instruction::new("INST", 4)
                .form(
                    InstructionForm::new("base")
                        .field(InstructionField::constant("10"))
                        .field(InstructionField::variable("mode", 1))
                        .field(InstructionField::variable("opcode", 1).merge_mode_uses()),
                )
                .form(
                    InstructionForm::new("other")
                        .field(InstructionField::constant("11"))
                        .field(InstructionField::variable("mode", 1))
                        .field(InstructionField::variable("opcode", 1).merge_mode_uses()),
                ),
            Instruction::new("UNUSED", 3).form(
                InstructionForm::new("base")
                    .field(InstructionField::constant("0"))
                    .field(InstructionField::variable("unused", 2)),
            ),
        ]);
        let program = vec![decode_one(&isa, "1000")];
        let max_candidate = ISACandidate::max_isa(&isa);
        let from_program_candidate = ISACandidate::from_program(&isa, &program);
        let mut rng = StdRng::seed_from_u64(0x5102);
        let random_candidate = ISACandidate::random_isa(&isa, &mut rng);

        assert_same_field_use_shape(&max_candidate, &from_program_candidate);
        assert_same_field_use_shape(&max_candidate, &random_candidate);
    }

    #[test]
    fn register_operand_fields_are_not_selectable_ga_genes() {
        let manager = manager_with(
            isa_with_instructions(vec![register_operand_instruction()]),
            StdRng::seed_from_u64(0x5103),
            HashMap::new(),
            vec![],
        );

        assert!(!manager.field_selectable_for_ga_restriction("rn"));
        assert!(manager.field_selectable_for_ga_restriction("mode"));
    }

    #[test]
    fn unrestricted_form_fields_are_not_selectable_ga_genes() {
        let manager = manager_with_forms(
            isa_with_instructions(vec![unrestricted_field_instruction()]),
            StdRng::seed_from_u64(0x5106),
            HashMap::new(),
            HashMap::from([("UNRES".to_string(), HashSet::from(["base".to_string()]))]),
            vec![],
        );

        assert!(!manager.field_selectable_for_ga_restriction("opcode"));
        assert!(manager.field_selectable_for_ga_restriction("mode"));
    }

    #[test]
    fn unrestricted_form_validation_is_encoding_order_insensitive() {
        let manager = manager_with_forms(
            isa_with_instructions(vec![two_uses_field_instruction()]),
            StdRng::seed_from_u64(0x510A),
            HashMap::new(),
            HashMap::from([("USES2".to_string(), HashSet::from(["base".to_string()]))]),
            vec![],
        );
        let candidate = candidate_with_active_forms(
            &[
                (
                    "left",
                    FieldUses::Uses {
                        name: "left".to_string(),
                        patterns: patterns(&["11", "10", "01", "00"]),
                        len: 2,
                    },
                ),
                (
                    "right",
                    FieldUses::Uses {
                        name: "right".to_string(),
                        patterns: patterns(&["10", "00", "11", "01"]),
                        len: 2,
                    },
                ),
            ],
            &[("USES2", &["base"])],
        );

        assert!(matches!(manager.valid_encodings(&candidate), Ok(_)));
    }

    #[test]
    fn children_do_not_swap_register_operand_field_uses() {
        let isa = isa_with_instructions(vec![register_operand_instruction()]);
        let mut manager = manager_with(isa, StdRng::seed_from_u64(0x5104), HashMap::new(), vec![]);
        manager.crossover_rate = 1.0;
        manager.crossover_gene_rate = 1.0;
        let parent1 = candidate_with_active_forms(
            &[
                ("rn", uses_field(&["00"])),
                ("mode", variable_bits_field("0")),
            ],
            &[("REG", &["base"])],
        );
        let parent2 = candidate_with_active_forms(
            &[
                ("rn", uses_field(&["11"])),
                ("mode", variable_bits_field("1")),
            ],
            &[("REG", &["base"])],
        );

        let (child1, child2) = manager.reproduce(&parent1, &parent2);

        assert_eq!(
            child1.valid_field_uses.get("rn"),
            parent1.valid_field_uses.get("rn")
        );
        assert_eq!(
            child2.valid_field_uses.get("rn"),
            parent2.valid_field_uses.get("rn")
        );
        assert_eq!(
            child1.valid_field_uses.get("mode"),
            parent2.valid_field_uses.get("mode")
        );
        assert_eq!(
            child2.valid_field_uses.get("mode"),
            parent1.valid_field_uses.get("mode")
        );
    }

    #[test]
    fn random_isa_candidate_preserves_unrestricted_form_fields_and_active_forms() {
        let mut manager = manager_with_forms(
            isa_with_instructions(vec![unrestricted_field_instruction()]),
            StdRng::seed_from_u64(0x5107),
            HashMap::new(),
            HashMap::from([("UNRES".to_string(), HashSet::from(["base".to_string()]))]),
            vec![],
        );

        for seed in 0..64 {
            manager.rng = StdRng::seed_from_u64(seed);
            let candidate = manager.random_isa_candidate();

            assert_eq!(
                candidate.valid_field_uses.get("opcode"),
                manager.max_isa_candidate.valid_field_uses.get("opcode")
            );
            assert!(
                candidate
                    .active_forms
                    .get("UNRES")
                    .is_some_and(|forms| forms.contains("base")),
                "unrestricted form should be active in random candidate"
            );
        }
    }

    #[test]
    fn mutate_preserves_unrestricted_form_fields_and_active_forms() {
        let mut manager = manager_with_forms(
            isa_with_instructions(vec![unrestricted_field_instruction()]),
            StdRng::seed_from_u64(0x5108),
            HashMap::new(),
            HashMap::from([("UNRES".to_string(), HashSet::from(["base".to_string()]))]),
            vec![],
        );
        manager.mutate_field_rate = 1.0;
        manager.mutate_form_rate = 1.0;
        let original = candidate_with_active_forms(
            &[
                ("opcode", uses_field(&["xx"])),
                ("mode", variable_bits_field("00")),
            ],
            &[("UNRES", &["base", "inactive"])],
        );

        for seed in 0..64 {
            manager.rng = StdRng::seed_from_u64(seed);
            let mutated = manager.mutate(original.clone());

            assert_eq!(
                mutated.valid_field_uses.get("opcode"),
                manager.max_isa_candidate.valid_field_uses.get("opcode")
            );
            assert!(
                mutated
                    .active_forms
                    .get("UNRES")
                    .is_some_and(|forms| forms.contains("base")),
                "unrestricted form should remain active after mutation"
            );
        }
    }

    #[test]
    fn children_do_not_swap_or_drop_unrestricted_form_fields() {
        let isa = isa_with_instructions(vec![unrestricted_field_instruction()]);
        let mut manager = manager_with_forms(
            isa,
            StdRng::seed_from_u64(0x5109),
            HashMap::new(),
            HashMap::from([("UNRES".to_string(), HashSet::from(["base".to_string()]))]),
            vec![],
        );
        manager.crossover_rate = 1.0;
        manager.crossover_gene_rate = 1.0;
        let parent1 = candidate_with_active_forms(
            &[
                ("opcode", uses_field(&["xx"])),
                ("mode", variable_bits_field("00")),
            ],
            &[("UNRES", &["base"])],
        );
        let parent2 = candidate_with_active_forms(
            &[
                ("opcode", uses_field(&["00"])),
                ("mode", variable_bits_field("11")),
            ],
            &[("UNRES", &["inactive"])],
        );

        let (child1, child2) = manager.reproduce(&parent1, &parent2);

        for child in [&child1, &child2] {
            assert_eq!(
                child.valid_field_uses.get("opcode"),
                manager.max_isa_candidate.valid_field_uses.get("opcode")
            );
            assert!(
                child
                    .active_forms
                    .get("UNRES")
                    .is_some_and(|forms| forms.contains("base")),
                "unrestricted form should remain active after crossover"
            );
        }
    }

    #[test]
    fn mutate_does_not_change_register_operand_field_uses() {
        let mut manager = manager_with(
            isa_with_instructions(vec![register_operand_instruction()]),
            StdRng::seed_from_u64(0x5105),
            HashMap::new(),
            vec![],
        );
        manager.mutate_field_rate = 1.0;
        manager.mutate_form_rate = 0.0;
        let original = candidate_with_active_forms(
            &[
                ("rn", uses_field(&["00"])),
                ("mode", variable_bits_field("0")),
            ],
            &[("REG", &["base"])],
        );

        let mutated = manager.mutate(original.clone());

        assert_eq!(
            mutated.valid_field_uses.get("rn"),
            original.valid_field_uses.get("rn")
        );
    }

    #[test]
    fn constructor_initializes_simulator_workspace_inputs_and_parameters() {
        let isa = isa_with_instructions(vec![one_field_instruction()]);
        let program = vec![decode_one(&isa, "10")];
        let isa = Box::leak(Box::new(isa));
        let mandatory_forms =
            HashMap::from([("INST".to_string(), HashSet::from(["base".to_string()]))]);
        let netlist_path = test_netlist_path();

        let manager = IsaOptimizationManager::new(
            isa,
            StdRng::seed_from_u64(0x5A5A),
            mandatory_forms.clone(),
            HashMap::new(),
            &netlist_path,
            "examples/NangateOpenCellLibrary_typical.lib",
            program.clone(),
            7,
            2,
            0.25,
            0.5,
            0.75,
            0.125,
        );

        assert!(manager.candidates.is_empty());
        assert!(manager.candidate_fitnesses.is_empty());
        assert_eq!(manager.mandatory_forms, mandatory_forms);
        assert_eq!(manager.program, program);
        assert_eq!(manager.population_size, 7);
        assert_eq!(manager.elite_candidate_count, 2);
        assert_eq!(manager.crossover_rate, 0.25);
        assert_eq!(manager.crossover_gene_rate, 0.5);
        assert_eq!(manager.mutate_field_rate, 0.75);
        assert_eq!(manager.mutate_form_rate, 0.125);
        assert!(manager
            .simulator
            .input_wire_names()
            .iter()
            .any(|name| name == "inst[0]"));
    }

    #[test]
    fn instruction_conflict_count_returns_zero_when_program_matches_candidate() {
        let isa = isa_with_instructions(vec![one_field_instruction()]);
        let program = vec![decode_one(&isa, "11")];
        let manager = manager_with(isa, StdRng::seed_from_u64(0x7000), HashMap::new(), program);
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );

        assert_eq!(manager.instruction_conflict_count(&candidate), 0);
    }

    #[test]
    fn instruction_conflict_count_counts_inactive_instruction_form() {
        let isa = isa_with_instructions(vec![one_field_instruction()]);
        let program = vec![decode_one(&isa, "11")];
        let manager = manager_with(isa, StdRng::seed_from_u64(0x7001), HashMap::new(), program);
        let candidate = candidate_with_active_forms(&[("bit", variable_bits_field("x"))], &[]);

        assert_eq!(manager.instruction_conflict_count(&candidate), 1);
    }

    #[test]
    fn instruction_conflict_count_counts_field_use_mismatch() {
        let isa = isa_with_instructions(vec![one_field_instruction()]);
        let program = vec![decode_one(&isa, "11")];
        let manager = manager_with(isa, StdRng::seed_from_u64(0x7002), HashMap::new(), program);
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("0"))],
            &[("INST", &["base"])],
        );

        assert_eq!(manager.instruction_conflict_count(&candidate), 1);
    }

    #[test]
    fn instruction_conflict_count_counts_each_conflicting_instruction() {
        let isa = isa_with_instructions(vec![one_field_instruction()]);
        let program = vec![decode_one(&isa, "10"), decode_one(&isa, "11")];
        let manager = manager_with(isa, StdRng::seed_from_u64(0x7003), HashMap::new(), program);
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("0"))],
            &[("INST", &["base"])],
        );

        assert_eq!(manager.instruction_conflict_count(&candidate), 1);
    }

    #[test]
    fn instruction_conflict_rate_returns_fraction_of_conflicting_instructions() {
        let isa = isa_with_instructions(vec![one_field_instruction()]);
        let program = vec![decode_one(&isa, "10"), decode_one(&isa, "11")];
        let manager = manager_with(isa, StdRng::seed_from_u64(0x7004), HashMap::new(), program);
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("0"))],
            &[("INST", &["base"])],
        );

        assert_eq!(manager.instruction_conflict_rate(&candidate), 0.5);
    }

    #[test]
    fn instruction_conflict_rate_is_zero_for_empty_program() {
        let manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7005),
            HashMap::new(),
            vec![],
        );
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );

        assert_eq!(manager.instruction_conflict_rate(&candidate), 0.0);
    }

    #[test]
    fn valid_encodings_returns_encodings_for_active_forms_only() {
        let manager = manager_with(
            isa_with_instructions(vec![two_form_instruction()]),
            StdRng::seed_from_u64(0x7100),
            HashMap::new(),
            vec![],
        );
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );

        assert_eq!(valid_encodings_ok(&manager, &candidate), patterns(&["1x"]));
    }

    #[test]
    fn valid_encodings_applies_candidate_field_uses() {
        let manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7101),
            HashMap::new(),
            vec![],
        );
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("0"))],
            &[("INST", &["base"])],
        );

        assert_eq!(valid_encodings_ok(&manager, &candidate), patterns(&["10"]));
    }

    #[test]
    fn valid_encodings_returns_empty_when_no_forms_are_active() {
        let manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7102),
            HashMap::new(),
            vec![],
        );
        let candidate = candidate_with_active_forms(&[("bit", variable_bits_field("x"))], &[]);

        assert!(valid_encodings_ok(&manager, &candidate).is_empty());
    }

    #[test]
    fn valid_encodings_accepts_candidate_matching_fixed_field_uses() {
        let manager = manager_with(
            isa_with_instructions(vec![uses_field_instruction()]),
            StdRng::seed_from_u64(0x710A),
            HashMap::new(),
            vec![],
        )
        .with_fixed_field_uses(HashMap::from([("opcode".to_string(), uses_field(&["xx"]))]));
        let candidate = candidate_with_active_forms(
            &[("opcode", uses_field(&["00", "01", "10", "11"]))],
            &[("USES", &["base"])],
        );

        assert_eq!(
            valid_encodings_ok(&manager, &candidate),
            patterns(&["100", "101", "110", "111"])
        );
    }

    #[test]
    fn valid_encodings_errors_when_candidate_violates_fixed_field_uses() {
        let manager = manager_with(
            isa_with_instructions(vec![uses_field_instruction()]),
            StdRng::seed_from_u64(0x710B),
            HashMap::new(),
            vec![],
        )
        .with_fixed_field_uses(HashMap::from([("opcode".to_string(), uses_field(&["xx"]))]));
        let candidate =
            candidate_with_active_forms(&[("opcode", uses_field(&["00"]))], &[("USES", &["base"])]);

        assert!(matches!(
            manager.valid_encodings(&candidate),
            Err(ISACandidateError::FixedFieldUsesError)
        ));
    }

    #[test]
    fn valid_encodings_errors_when_mandatory_form_is_inactive() {
        let mandatory_forms =
            HashMap::from([("INST".to_string(), HashSet::from(["base".to_string()]))]);
        let manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7103),
            mandatory_forms,
            vec![],
        );
        let candidate = candidate_with_active_forms(&[("bit", variable_bits_field("x"))], &[]);

        assert!(matches!(
            manager.valid_encodings(&candidate),
            Err(ISACandidateError::MandatoryFormsError)
        ));
    }

    #[test]
    fn valid_encodings_errors_when_mandatory_instruction_has_no_active_encodings() {
        let mandatory_forms = HashMap::from([("INST".to_string(), HashSet::new())]);
        let manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7104),
            mandatory_forms,
            vec![],
        );
        let candidate = candidate_with_active_forms(&[("bit", variable_bits_field("x"))], &[]);

        assert!(matches!(
            manager.valid_encodings(&candidate),
            Err(ISACandidateError::MandatoryFormsError)
        ));
    }

    #[test]
    fn valid_encodings_accepts_unrestricted_active_unconstrained_form() {
        let unrestricted_forms =
            HashMap::from([("INST".to_string(), HashSet::from(["base".to_string()]))]);
        let manager = manager_with_forms(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7105),
            HashMap::new(),
            unrestricted_forms,
            vec![],
        );
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );

        assert_eq!(valid_encodings_ok(&manager, &candidate), patterns(&["1x"]));
    }

    #[test]
    fn valid_encodings_errors_when_unrestricted_form_is_inactive() {
        let unrestricted_forms =
            HashMap::from([("INST".to_string(), HashSet::from(["base".to_string()]))]);
        let manager = manager_with_forms(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7106),
            HashMap::new(),
            unrestricted_forms,
            vec![],
        );
        let candidate = candidate_with_active_forms(&[("bit", variable_bits_field("x"))], &[]);

        assert!(matches!(
            manager.valid_encodings(&candidate),
            Err(ISACandidateError::UnrestrictedFormsError)
        ));
    }

    #[test]
    fn valid_encodings_errors_when_unrestricted_variable_bits_field_is_restricted() {
        let unrestricted_forms =
            HashMap::from([("INST".to_string(), HashSet::from(["base".to_string()]))]);
        let manager = manager_with_forms(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7107),
            HashMap::new(),
            unrestricted_forms,
            vec![],
        );
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("0"))],
            &[("INST", &["base"])],
        );

        assert!(matches!(
            manager.valid_encodings(&candidate),
            Err(ISACandidateError::UnrestrictedFormsError)
        ));
    }

    #[test]
    fn valid_encodings_errors_when_unrestricted_uses_field_is_restricted() {
        let unrestricted_forms =
            HashMap::from([("USES".to_string(), HashSet::from(["base".to_string()]))]);
        let manager = manager_with_forms(
            isa_with_instructions(vec![uses_field_instruction()]),
            StdRng::seed_from_u64(0x7108),
            HashMap::new(),
            unrestricted_forms,
            vec![],
        );
        let candidate =
            candidate_with_active_forms(&[("opcode", uses_field(&["00"]))], &[("USES", &["base"])]);

        assert!(matches!(
            manager.valid_encodings(&candidate),
            Err(ISACandidateError::UnrestrictedFormsError)
        ));
    }

    #[test]
    fn valid_encodings_errors_when_static_instruction_form_is_inactive() {
        let isa = isa_with_instructions(vec![one_field_instruction()]);
        let program = vec![static_decode_one(&isa, "10")];
        let manager = manager_with(isa, StdRng::seed_from_u64(0x7109), HashMap::new(), program);
        let candidate = candidate_with_active_forms(&[("bit", variable_bits_field("x"))], &[]);

        assert!(matches!(
            manager.valid_encodings(&candidate),
            Err(ISACandidateError::StaticInstructionError)
        ));
    }

    #[test]
    fn valid_encodings_errors_when_static_instruction_field_is_restricted() {
        let isa = isa_with_instructions(vec![one_field_instruction()]);
        let program = vec![static_decode_one(&isa, "10")];
        let manager = manager_with(isa, StdRng::seed_from_u64(0x7110), HashMap::new(), program);
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("1"))],
            &[("INST", &["base"])],
        );

        assert!(matches!(
            manager.valid_encodings(&candidate),
            Err(ISACandidateError::StaticInstructionError)
        ));
    }

    #[test]
    fn gate_removal_count_returns_count_no_larger_than_total_gate_count() {
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7200),
            HashMap::new(),
            vec![],
        );
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );

        let gate_count = match manager.gate_removal_count(&candidate) {
            Ok(count) => count,
            Err(err) => {
                panic!("gate_removal_count unexpectedly rejected candidate: {err:?}")
            }
        };

        assert!(gate_count <= manager.simulator.combinational_gate_count());
    }

    #[test]
    fn gate_removal_count_returns_count_for_empty_encoding_set() {
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7201),
            HashMap::new(),
            vec![],
        );
        let candidate = candidate_with_active_forms(&[("bit", variable_bits_field("x"))], &[]);

        let gate_count = match manager.gate_removal_count(&candidate) {
            Ok(count) => count,
            Err(err) => {
                panic!("gate_removal_count unexpectedly rejected candidate: {err:?}")
            }
        };

        assert!(gate_count <= manager.simulator.combinational_gate_count());
    }

    #[test]
    fn core_area_reduction_frac_is_gate_removal_count_over_total_gates() {
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7202),
            HashMap::new(),
            vec![],
        );
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );

        let removed = match manager.gate_removal_count(&candidate) {
            Ok(count) => count,
            Err(err) => {
                panic!("gate_removal_count unexpectedly rejected candidate: {err:?}")
            }
        };
        let fraction = match manager.core_area_reduction_frac(&candidate) {
            Ok(fraction) => fraction,
            Err(err) => {
                panic!("core_area_reduction_frac unexpectedly rejected candidate: {err:?}")
            }
        };

        assert_eq!(
            fraction,
            removed as f64 / manager.simulator.combinational_gate_count() as f64
        );
        assert!((0.0..=1.0).contains(&fraction));
    }

    #[test]
    fn candidate_fitness_combines_area_reward_and_unmodified_program_reward() {
        let isa = isa_with_instructions(vec![one_field_instruction()]);
        let program = vec![decode_one(&isa, "10"), decode_one(&isa, "11")];
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("0"))],
            &[("INST", &["base"])],
        );

        let mut expected_manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7300),
            HashMap::new(),
            program.clone(),
        );
        let area_reduction = match expected_manager.core_area_reduction_frac(&candidate) {
            Ok(area_reduction) => area_reduction,
            Err(err) => {
                panic!("candidate should produce valid encodings: {err:?}")
            }
        };
        let expected = area_reduction * WEIGHT_CORE_SIZE
            + (1.0 - expected_manager.instruction_conflict_rate(&candidate))
                * WEIGHT_UNMODIFIED_PROGRAM;

        let mut fitness_manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7300),
            HashMap::new(),
            program,
        );
        let fitness = match fitness_manager.candidate_fitness(&candidate) {
            Ok(fitness) => fitness,
            Err(err) => {
                panic!("candidate should produce valid encodings: {err:?}")
            }
        };

        assert_eq!(fitness, expected);
    }

    #[test]
    fn candidate_fitness_propagates_mandatory_form_errors() {
        let mandatory_forms =
            HashMap::from([("INST".to_string(), HashSet::from(["base".to_string()]))]);
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7301),
            mandatory_forms,
            vec![],
        );
        let candidate = candidate_with_active_forms(&[("bit", variable_bits_field("x"))], &[]);

        assert!(matches!(
            manager.candidate_fitness(&candidate),
            Err(ISACandidateError::MandatoryFormsError)
        ));
    }

    #[test]
    fn gate_area_and_fitness_propagate_unrestricted_form_errors() {
        let unrestricted_forms =
            HashMap::from([("INST".to_string(), HashSet::from(["base".to_string()]))]);
        let mut manager = manager_with_forms(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7302),
            HashMap::new(),
            unrestricted_forms,
            vec![],
        );
        let candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("0"))],
            &[("INST", &["base"])],
        );

        assert!(matches!(
            manager.gate_removal_count(&candidate),
            Err(ISACandidateError::UnrestrictedFormsError)
        ));
        assert!(matches!(
            manager.core_area_reduction_frac(&candidate),
            Err(ISACandidateError::UnrestrictedFormsError)
        ));
        assert!(matches!(
            manager.candidate_fitness(&candidate),
            Err(ISACandidateError::UnrestrictedFormsError)
        ));
    }

    #[test]
    fn set_initial_generation_seeds_max_and_program_minimum_candidates() {
        let isa = isa_with_instructions(vec![one_field_instruction()]);
        let program = vec![decode_one(&isa, "10")];
        let mut manager = manager_with(isa, StdRng::seed_from_u64(0x7340), HashMap::new(), program);
        manager.population_size = 4;
        manager.candidates = vec![candidate_with_active_forms(
            &[("bit", variable_bits_field("0"))],
            &[("INST", &[])],
        )];
        manager.candidate_fitnesses = vec![999.0];
        let max_candidate = ISACandidate::max_isa(manager.isa);
        let min_candidate = ISACandidate::from_program(manager.isa, &manager.program);

        manager.set_initial_generation();

        assert_eq!(manager.candidates.len(), 4);
        assert_eq!(manager.candidate_fitnesses.len(), 4);
        assert_eq!(manager.candidates.first(), Some(&max_candidate));
        assert_eq!(manager.candidates.get(1), Some(&min_candidate));
        assert!(manager
            .candidate_fitnesses
            .iter()
            .all(|fitness| *fitness != 999.0));
        let candidates = manager.candidates.clone();
        let fitnesses = manager.candidate_fitnesses.clone();
        assert!(candidates
            .iter()
            .zip(fitnesses)
            .all(|(candidate, fitness)| manager.candidate_fitness(candidate) == Ok(fitness)));
    }

    #[test]
    fn new_generation_replaces_candidates_and_fitness_with_requested_population_size() {
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7350),
            HashMap::new(),
            vec![],
        );
        manager.population_size = 3;
        manager.crossover_rate = 0.0;
        manager.mutate_field_rate = 0.0;
        manager.mutate_form_rate = 0.0;
        let parent = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );
        manager.candidates = vec![parent.clone()];
        manager.candidate_fitnesses = vec![1.0];

        manager.new_generation();

        assert_eq!(manager.candidates.len(), 3);
        assert_eq!(manager.candidate_fitnesses.len(), 3);
        assert!(manager
            .candidates
            .iter()
            .all(|candidate| candidate == &parent));
    }

    #[test]
    fn new_generation_recomputes_fitness_for_new_candidates() {
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7351),
            HashMap::new(),
            vec![],
        );
        manager.population_size = 2;
        manager.crossover_rate = 0.0;
        manager.mutate_field_rate = 0.0;
        manager.mutate_form_rate = 0.0;
        let parent = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );
        manager.candidates = vec![parent];
        manager.candidate_fitnesses = vec![123.0];

        manager.new_generation();
        let children = manager.candidates.clone();
        let stored_fitness = manager.candidate_fitnesses.clone();
        let recomputed_fitness: Vec<_> = children
            .iter()
            .map(|candidate| match manager.candidate_fitness(candidate) {
                Ok(fitness) => fitness,
                Err(err) => {
                    panic!("new_generation produced an invalid child: {err:?}")
                }
            })
            .collect();

        assert_eq!(stored_fitness, recomputed_fitness);
        assert_ne!(stored_fitness, vec![123.0, 123.0]);
    }

    #[test]
    fn new_generation_keeps_best_elite_candidate_unchanged() {
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7354),
            HashMap::new(),
            vec![],
        );
        manager.population_size = 3;
        manager.elite_candidate_count = 1;
        manager.crossover_rate = 0.0;
        manager.mutate_field_rate = 0.0;
        manager.mutate_form_rate = 0.0;
        let lower_fitness_candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("0"))],
            &[("INST", &["base"])],
        );
        let elite_candidate = candidate_with_active_forms(
            &[("bit", variable_bits_field("1"))],
            &[("INST", &["base"])],
        );
        manager.candidates = vec![lower_fitness_candidate, elite_candidate.clone()];
        manager.candidate_fitnesses = vec![1.0, 10.0];

        manager.new_generation();

        assert_eq!(manager.candidates.first(), Some(&elite_candidate));
        assert_eq!(manager.candidate_fitnesses.first(), Some(&10.0));
        assert_eq!(manager.candidates.len(), 3);
        assert_eq!(manager.candidate_fitnesses.len(), 3);
    }

    #[test]
    fn new_generation_keeps_multiple_elites() {
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7355),
            HashMap::new(),
            vec![],
        );
        manager.population_size = 3;
        manager.elite_candidate_count = 2;
        manager.crossover_rate = 0.0;
        manager.mutate_field_rate = 0.0;
        manager.mutate_form_rate = 0.0;
        let lowest =
            candidate_with_active_forms(&[("bit", variable_bits_field("0"))], &[("INST", &[])]);
        let highest = candidate_with_active_forms(
            &[("bit", variable_bits_field("1"))],
            &[("INST", &["base"])],
        );
        let middle = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );
        manager.candidates = vec![lowest, highest.clone(), middle.clone()];
        manager.candidate_fitnesses = vec![1.0, 9.0, 4.0];

        manager.new_generation();

        assert!(manager.candidates.contains(&highest));
        assert!(manager.candidates.contains(&middle));
        assert_eq!(manager.candidates.len(), 3);
        assert_eq!(manager.candidate_fitnesses.len(), 3);
        assert!(manager.candidate_fitnesses.contains(&9.0));
        assert!(manager.candidate_fitnesses.contains(&4.0));
    }

    #[test]
    fn new_generation_does_not_select_zero_weight_candidates() {
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7352),
            HashMap::new(),
            vec![],
        );
        manager.population_size = 4;
        manager.crossover_rate = 0.0;
        manager.mutate_field_rate = 0.0;
        manager.mutate_form_rate = 0.0;
        let zero_weight_parent = candidate_with_active_forms(
            &[("bit", variable_bits_field("0"))],
            &[("INST", &["base"])],
        );
        let selected_parent = candidate_with_active_forms(
            &[("bit", variable_bits_field("1"))],
            &[("INST", &["base"])],
        );
        manager.candidates = vec![zero_weight_parent, selected_parent.clone()];
        manager.candidate_fitnesses = vec![0.0, 1.0];

        manager.new_generation();

        assert_eq!(manager.candidates.len(), 4);
        assert!(manager
            .candidates
            .iter()
            .all(|candidate| candidate == &selected_parent));
    }

    #[test]
    #[should_panic(expected = "WeightedIndex not created")]
    fn new_generation_panics_when_all_parent_fitnesses_are_zero() {
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7353),
            HashMap::new(),
            vec![],
        );
        manager.population_size = 1;
        manager.candidates = vec![candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        )];
        manager.candidate_fitnesses = vec![0.0];

        manager.new_generation();
    }

    #[test]
    fn children_return_parent_clones_when_crossover_rate_is_zero() {
        let mut manager = manager_with(
            isa_with_instructions(vec![two_form_instruction()]),
            StdRng::seed_from_u64(0x7400),
            HashMap::new(),
            vec![],
        );
        manager.crossover_rate = 0.0;
        let parent1 = candidate_with_active_forms(
            &[("bit", variable_bits_field("0"))],
            &[("INST", &["base"])],
        );
        let parent2 = candidate_with_active_forms(
            &[("bit", variable_bits_field("1"))],
            &[("INST", &["inactive"])],
        );

        let (child1, child2) = manager.reproduce(&parent1, &parent2);

        assert_eq!(child1, parent1);
        assert_eq!(child2, parent2);
    }

    #[test]
    fn children_do_not_mutate_parent_candidates() {
        let mut manager = manager_with(
            isa_with_instructions(vec![two_form_instruction()]),
            StdRng::seed_from_u64(0x7401),
            HashMap::new(),
            vec![],
        );
        manager.crossover_rate = 1.0;
        manager.crossover_gene_rate = 1.0;
        let parent1 = candidate_with_active_forms(
            &[("bit", variable_bits_field("0"))],
            &[("INST", &["base"])],
        );
        let parent2 = candidate_with_active_forms(
            &[("bit", variable_bits_field("1"))],
            &[("INST", &["inactive"])],
        );
        let original_parent1 = parent1.clone();
        let original_parent2 = parent2.clone();

        let _ = manager.reproduce(&parent1, &parent2);

        assert_eq!(parent1, original_parent1);
        assert_eq!(parent2, original_parent2);
    }

    #[test]
    fn children_can_swap_valid_field_uses_between_parents() {
        let parent1 = candidate_with_active_forms(
            &[
                ("bit", variable_bits_field("0")),
                ("opcode", uses_field(&["00"])),
            ],
            &[("INST", &["base"])],
        );
        let parent2 = candidate_with_active_forms(
            &[
                ("bit", variable_bits_field("1")),
                ("opcode", uses_field(&["11"])),
            ],
            &[("INST", &["base"])],
        );
        let mut saw_field_swap = false;

        for seed in 0..256 {
            let mut manager = manager_with(
                isa_with_instructions(vec![one_field_instruction()]),
                StdRng::seed_from_u64(seed),
                HashMap::new(),
                vec![],
            );
            manager.crossover_rate = 1.0;
            manager.crossover_gene_rate = 1.0;
            let (child1, child2) = manager.reproduce(&parent1, &parent2);

            if child1.valid_field_uses.get("bit") == parent2.valid_field_uses.get("bit") {
                assert_eq!(
                    child2.valid_field_uses.get("bit"),
                    parent1.valid_field_uses.get("bit")
                );
                saw_field_swap = true;
                break;
            }
        }

        assert!(
            saw_field_swap,
            "expected some seed to swap a field-use gene"
        );
    }

    #[test]
    fn children_can_swap_active_forms_between_parents() {
        let parent1 = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );
        let parent2 = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["inactive"])],
        );
        let mut saw_form_swap = false;

        for seed in 0..256 {
            let mut manager = manager_with(
                isa_with_instructions(vec![two_form_instruction()]),
                StdRng::seed_from_u64(seed),
                HashMap::new(),
                vec![],
            );
            manager.crossover_rate = 1.0;
            manager.crossover_gene_rate = 1.0;
            let (child1, child2) = manager.reproduce(&parent1, &parent2);

            if child1.active_forms.get("INST") == parent2.active_forms.get("INST") {
                assert_eq!(
                    child2.active_forms.get("INST"),
                    parent1.active_forms.get("INST")
                );
                saw_form_swap = true;
                break;
            }
        }

        assert!(
            saw_form_swap,
            "expected some seed to swap an active-form gene"
        );
    }

    #[test]
    fn children_swap_empty_active_form_sets_when_keys_exist() {
        let parent1 =
            candidate_with_active_forms(&[("bit", variable_bits_field("x"))], &[("INST", &[])]);
        let parent2 = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );
        let mut saw_empty_set_swap = false;

        for seed in 0..256 {
            let mut manager = manager_with(
                isa_with_instructions(vec![one_field_instruction()]),
                StdRng::seed_from_u64(seed),
                HashMap::new(),
                vec![],
            );
            manager.crossover_rate = 1.0;
            manager.crossover_gene_rate = 1.0;
            let (child1, child2) = manager.reproduce(&parent1, &parent2);

            if child1.active_forms.get("INST") == parent2.active_forms.get("INST") {
                let child2_forms = child2
                    .active_forms
                    .get("INST")
                    .expect("active-form key should remain present");
                assert!(child2_forms.is_empty());
                saw_empty_set_swap = true;
                break;
            }
        }

        assert!(
            saw_empty_set_swap,
            "expected some seed to swap an empty active-form set"
        );
    }

    #[test]
    #[should_panic(expected = "active_forms should contain all instructions")]
    fn children_panic_when_parent_active_form_key_is_missing() {
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7403),
            HashMap::new(),
            vec![],
        );
        manager.crossover_rate = 1.0;
        manager.crossover_gene_rate = 1.0;
        let parent1 = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );
        let parent2 = candidate_with_active_forms(&[("bit", variable_bits_field("x"))], &[]);

        let _ = manager.reproduce(&parent1, &parent2);
    }

    #[test]
    #[should_panic]
    fn children_panic_when_parent_field_keys_differ() {
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7402),
            HashMap::new(),
            vec![],
        );
        manager.crossover_rate = 1.0;
        manager.crossover_gene_rate = 1.0;
        let parent1 = candidate_with_active_forms(
            &[("bit", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );
        let parent2 = candidate_with_active_forms(
            &[("other", variable_bits_field("x"))],
            &[("INST", &["base"])],
        );

        let _ = manager.reproduce(&parent1, &parent2);
    }

    #[test]
    fn mutate_active_forms_resamples_valid_subset_when_none_are_active() {
        let valid_forms = HashSet::from(["base".to_string(), "inactive".to_string()]);
        let mut manager = manager_with(
            isa_with_instructions(vec![two_form_instruction()]),
            StdRng::seed_from_u64(0x7500),
            HashMap::new(),
            vec![],
        );

        let mutated = manager.mutate_active_forms("INST", HashSet::new());

        assert!(
            mutated.iter().all(|form| valid_forms.contains(form)),
            "mutate_active_forms returned an unknown form: {mutated:?}"
        );
        assert!(mutated.len() <= valid_forms.len());
    }

    #[test]
    fn mutate_active_forms_resamples_valid_subset_when_all_forms_are_active() {
        let valid_forms = HashSet::from(["base".to_string(), "inactive".to_string()]);
        let mut manager = manager_with(
            isa_with_instructions(vec![two_form_instruction()]),
            StdRng::seed_from_u64(0x7501),
            HashMap::new(),
            vec![],
        );
        let active_forms = HashSet::from(["base".to_string(), "inactive".to_string()]);

        let mutated = manager.mutate_active_forms("INST", active_forms);

        assert!(
            mutated.iter().all(|form| valid_forms.contains(form)),
            "mutate_active_forms returned an unknown form: {mutated:?}"
        );
        assert!(mutated.len() <= valid_forms.len());
    }

    #[test]
    fn mutate_active_forms_only_returns_valid_forms() {
        let valid_forms = HashSet::from(["base".to_string(), "inactive".to_string()]);
        let mut manager = manager_with(
            isa_with_instructions(vec![two_form_instruction()]),
            StdRng::seed_from_u64(0),
            HashMap::new(),
            vec![],
        );

        for seed in 0..128 {
            manager.rng = StdRng::seed_from_u64(seed);
            let mutated = manager.mutate_active_forms("INST", HashSet::from(["base".to_string()]));

            assert!(
                mutated.iter().all(|form| valid_forms.contains(form)),
                "mutate_active_forms returned an unknown form: {mutated:?}"
            );
        }
    }

    #[test]
    fn mutate_active_forms_samples_empty_partial_and_full_subsets() {
        let valid_forms = HashSet::from(["base".to_string(), "inactive".to_string()]);
        let mut saw_empty = false;
        let mut saw_partial = false;
        let mut saw_full = false;

        for seed in 0..512 {
            let mut manager = manager_with(
                isa_with_instructions(vec![two_form_instruction()]),
                StdRng::seed_from_u64(seed),
                HashMap::new(),
                vec![],
            );
            let mutated = manager.mutate_active_forms("INST", HashSet::from(["base".to_string()]));

            assert!(
                mutated.iter().all(|form| valid_forms.contains(form)),
                "mutate_active_forms returned an unknown form: {mutated:?}"
            );
            match mutated.len() {
                0 => saw_empty = true,
                1 => saw_partial = true,
                2 => saw_full = true,
                len => panic!("expected at most two active forms, got len {len}"),
            }

            if saw_empty && saw_partial && saw_full {
                break;
            }
        }

        assert!(saw_empty, "expected some seed to sample no active forms");
        assert!(saw_partial, "expected some seed to sample one active form");
        assert!(saw_full, "expected some seed to sample all active forms");
    }

    #[test]
    #[should_panic(expected = "instruction_name must be a valid instruction in the ISA")]
    fn mutate_active_forms_panics_for_unknown_instruction() {
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7502),
            HashMap::new(),
            vec![],
        );

        let _ = manager.mutate_active_forms("UNKNOWN", HashSet::new());
    }

    #[test]
    fn mutate_returns_candidate_unchanged_when_all_mutation_rates_are_zero() {
        let mut manager = manager_with(
            isa_with_instructions(vec![two_form_instruction()]),
            StdRng::seed_from_u64(0x7600),
            HashMap::new(),
            vec![],
        );
        manager.mutate_field_rate = 0.0;
        manager.mutate_form_rate = 0.0;
        let original = candidate_with_active_forms(
            &[
                ("imm", variable_bits_field("0")),
                ("opcode", uses_field(&["00"])),
            ],
            &[("INST", &["base"])],
        );

        let mutated = manager.mutate(original.clone());

        assert_eq!(mutated, original);
    }

    #[test]
    fn mutate_can_change_field_uses_and_resample_active_forms_in_one_call() {
        let valid_forms = HashSet::from(["base".to_string(), "inactive".to_string()]);
        let mut manager = manager_with(
            isa_with_instructions(vec![two_form_instruction()]),
            StdRng::seed_from_u64(0x7601),
            HashMap::new(),
            vec![],
        );
        manager.mutate_field_rate = 1.0;
        manager.mutate_form_rate = 1.0;
        let original = candidate_with_active_forms(
            &[("bit", variable_bits_field("0"))],
            &[("INST", &["base"])],
        );

        let mutated = manager.mutate(original.clone());

        assert_ne!(mutated.valid_field_uses, original.valid_field_uses);
        let mutated_forms = mutated
            .active_forms
            .get("INST")
            .expect("mutated candidate should preserve the instruction active_forms key");
        assert!(
            mutated_forms.iter().all(|form| valid_forms.contains(form)),
            "mutate active forms returned an unknown form: {mutated_forms:?}"
        );
        assert!(mutated_forms.len() <= valid_forms.len());
    }

    #[test]
    #[should_panic(expected = "All instructions should have a key in ISACandidate::active_forms")]
    fn mutate_panics_when_form_mutation_requires_missing_active_forms_entry() {
        let mut manager = manager_with(
            isa_with_instructions(vec![one_field_instruction()]),
            StdRng::seed_from_u64(0x7602),
            HashMap::new(),
            vec![],
        );
        manager.mutate_field_rate = 0.0;
        manager.mutate_form_rate = 1.0;
        let original = candidate(&[("bit", variable_bits_field("x"))]);

        let _ = manager.mutate(original);
    }

    #[test]
    fn mutate_updates_the_only_variable_bits_field() {
        let mut manager = manager(StdRng::seed_from_u64(0x6001));
        let original = candidate(&[("imm", variable_bits_field("0"))]);
        let mutated = manager.mutate(original);
        let field = mutated
            .valid_field_uses
            .get("imm")
            .expect("mutated candidate should keep imm field");

        let FieldUses::VariableBits { pattern, .. } = field else {
            panic!("expected VariableBits field");
        };
        let pattern = pattern
            .as_ref()
            .expect("mutating a populated VariableBits field should keep a pattern for this seed");
        assert!(
            pattern == &BitPattern::parse("1") || pattern == &BitPattern::parse("x"),
            "expected Low bit to flip to High or generalize to Var, got {pattern:?}"
        );
    }

    #[test]
    fn mutate_updates_the_only_uses_field_and_preserves_len() {
        let mut manager = manager(StdRng::seed_from_u64(0x6002));
        let original = candidate(&[("opcode", uses_field(&["00"]))]);
        let mutated = manager.mutate(original);
        let field = mutated
            .valid_field_uses
            .get("opcode")
            .expect("mutated candidate should keep opcode field");
        let FieldUses::Uses { patterns, len, .. } = field else {
            panic!("expected Uses field");
        };

        assert_eq!(*len, 2);
        assert!(patterns.iter().all(|pattern| pattern.len() == *len));
        assert_ne!(patterns, &self::patterns(&["00"]));
    }

    #[test]
    fn mutate_with_field_rate_one_updates_every_field() {
        let original = candidate(&[
            ("a", variable_bits_field("0")),
            ("b", variable_bits_field("1")),
        ]);

        let mut manager = manager(StdRng::seed_from_u64(0));
        manager.mutate_field_rate = 1.0;
        let mutated = manager.mutate(original.clone());

        assert_ne!(
            mutated.valid_field_uses.get("a"),
            original.valid_field_uses.get("a")
        );
        assert_ne!(
            mutated.valid_field_uses.get("b"),
            original.valid_field_uses.get("b")
        );
    }

    #[test]
    fn mutate_keeps_all_candidate_field_names() {
        let original = candidate(&[
            ("imm", variable_bits_field("x")),
            ("opcode", uses_field(&["00", "11"])),
        ]);
        let mut manager = manager(StdRng::seed_from_u64(0x6003));
        let mutated = manager.mutate(original);

        assert!(mutated.valid_field_uses.contains_key("imm"));
        assert!(mutated.valid_field_uses.contains_key("opcode"));
        assert_eq!(mutated.valid_field_uses.len(), 2);
    }

    #[test]
    fn mutate_preserves_uses_length_metadata_when_that_field_is_selected() {
        let original = candidate(&[
            ("imm", variable_bits_field("1")),
            ("opcode", uses_field(&["00x"])),
        ]);
        let mut saw_opcode_mutation = false;

        let mut manager = manager(StdRng::seed_from_u64(0));
        for seed in 0..512 {
            manager.rng = StdRng::seed_from_u64(seed);
            let mutated = manager.mutate(original.clone());
            if mutated.valid_field_uses.get("opcode") != original.valid_field_uses.get("opcode") {
                let FieldUses::Uses { patterns, len, .. } = mutated
                    .valid_field_uses
                    .get("opcode")
                    .expect("opcode field should remain present")
                else {
                    panic!("expected Uses field");
                };

                assert_eq!(*len, 3);
                assert!(patterns.iter().all(|pattern| pattern.len() == *len));
                saw_opcode_mutation = true;
                break;
            }
        }

        assert!(saw_opcode_mutation, "expected some seed to mutate opcode");
    }

    #[test]
    fn mutate_can_remove_variable_bits_pattern() {
        let original = candidate(&[("imm", variable_bits_field("101"))]);
        let mut manager = manager(StdRng::seed_from_u64(0));
        manager.mutate_field_rate = 1.0;
        manager.mutate_form_rate = 0.0;

        for seed in 0..10_000 {
            manager.rng = StdRng::seed_from_u64(seed);
            let mutated = manager.mutate(original.clone());
            let FieldUses::VariableBits { pattern, len, .. } = mutated
                .valid_field_uses
                .get("imm")
                .expect("mutated candidate should keep imm field")
            else {
                panic!("expected VariableBits field");
            };

            assert_eq!(*len, 3);
            if pattern.is_none() {
                return;
            }
        }

        panic!("expected some deterministic seed to remove a VariableBits pattern");
    }

    #[test]
    fn mutate_allows_empty_field_uses_when_form_mutation_is_disabled() {
        let mut manager = manager(StdRng::seed_from_u64(0x6004));
        manager.mutate_field_rate = 1.0;
        manager.mutate_form_rate = 0.0;
        let mutated = manager.mutate(ISACandidate {
            valid_field_uses: HashMap::new(),
            active_forms: HashMap::new(),
        });

        assert!(mutated.valid_field_uses.is_empty());
        assert!(mutated.active_forms.is_empty());
    }

    #[test]
    fn mutate_field_variable_bits_flips_low_to_high() {
        let mut manager = manager(StdRng::seed_from_u64(0x10));
        let mutated = unwrap_variable_bits(manager.mutate_field(variable_bits_field("0"), 1));

        assert_eq!(mutated, BitPattern::parse("1"));
    }

    #[test]
    fn mutate_field_variable_bits_flips_high_to_low() {
        let mut manager = manager(StdRng::seed_from_u64(0x11));
        let mutated = unwrap_variable_bits(manager.mutate_field(variable_bits_field("1"), 1));

        assert_eq!(mutated, BitPattern::parse("0"));
    }

    #[test]
    fn mutate_field_variable_bits_materializes_var_to_concrete_bit() {
        let mut manager = manager(StdRng::seed_from_u64(0x12));
        let mutated = unwrap_variable_bits(manager.mutate_field(variable_bits_field("x"), 1));

        assert_concrete(&mutated);
    }

    #[test]
    fn mutate_field_variable_bits_preserves_name_and_width() {
        let mut manager = manager(StdRng::seed_from_u64(0x13));
        let mutated = manager.mutate_field(variable_bits_field("101"), 3);
        let FieldUses::VariableBits { name, pattern, len } = mutated else {
            panic!("expected VariableBits field");
        };

        assert_eq!(name, "field");
        assert_eq!(len, 3);
        assert_eq!(
            pattern
                .as_ref()
                .expect("mutated VariableBits should remain populated for this seed")
                .len(),
            3
        );
    }

    #[test]
    fn mutate_field_variable_bits_can_be_removed() {
        let field = variable_bits_field("101");
        let mut manager = manager(StdRng::seed_from_u64(0));

        for seed in 0..10_000 {
            manager.rng = StdRng::seed_from_u64(seed);
            let mutated = manager.mutate_field(field.clone(), 3);
            let FieldUses::VariableBits { pattern, len, .. } = mutated else {
                panic!("expected VariableBits field");
            };

            assert_eq!(len, 3);
            if pattern.is_none() {
                return;
            }
        }

        panic!("expected some deterministic seed to remove a VariableBits pattern");
    }

    #[test]
    fn mutate_field_empty_variable_bits_creates_random_pattern() {
        let mut manager = manager(StdRng::seed_from_u64(0x1313));
        let mutated = manager.mutate_field(empty_variable_bits_field(4), 4);
        let FieldUses::VariableBits { pattern, len, .. } = mutated else {
            panic!("expected VariableBits field");
        };

        assert_eq!(len, 4);
        assert_eq!(
            pattern
                .as_ref()
                .expect("empty VariableBits should be repopulated by mutation")
                .len(),
            4
        );
    }

    #[test]
    fn mutate_field_variable_bits_selects_bit_positions_roughly_uniformly() {
        let mut manager = manager(StdRng::seed_from_u64(0x14));
        let field = variable_bits_field("000");
        let sample_count = 6_000usize;
        let expected_count = sample_count / 3;
        let tolerance = expected_count / 5;
        let mut counts = [0usize; 3];

        let mut observed = 0usize;
        while observed < sample_count {
            let FieldUses::VariableBits { pattern, .. } = manager.mutate_field(field.clone(), 3)
            else {
                panic!("expected VariableBits field");
            };
            let Some(mutated) = pattern else {
                continue;
            };
            let changed_idx = mutated
                .bits
                .iter()
                .position(|bit| *bit != Bit::Low)
                .expect("one Low bit should flip or generalize");
            counts[changed_idx] += 1;
            observed += 1;
        }

        for count in counts {
            assert!(
                expected_count.abs_diff(count) <= tolerance,
                "expected count {count} to be within {tolerance} of {expected_count}"
            );
        }
    }

    #[test]
    fn mutate_field_variable_bits_materializes_var_values_roughly_uniformly() {
        let mut manager = manager(StdRng::seed_from_u64(0x15));
        let field = variable_bits_field("x");
        let sample_count = 4_000usize;
        let expected_count = sample_count / 2;
        let tolerance = expected_count / 5;
        let mut low_count = 0usize;
        let mut high_count = 0usize;

        let mut observed = 0usize;
        while observed < sample_count {
            let FieldUses::VariableBits { pattern, .. } = manager.mutate_field(field.clone(), 1)
            else {
                panic!("expected VariableBits field");
            };
            let Some(mutated) = pattern else {
                continue;
            };
            match mutated.bits[0] {
                Bit::Low => low_count += 1,
                Bit::High => high_count += 1,
                other => panic!("expected concrete bit, got {other:?}"),
            }
            observed += 1;
        }

        assert!(expected_count.abs_diff(low_count) <= tolerance);
        assert!(expected_count.abs_diff(high_count) <= tolerance);
    }

    #[test]
    fn mutate_field_uses_subtracts_selected_concrete_point_from_variable_pattern() {
        let mut manager = manager(StdRng::seed_from_u64(0x16));
        let mutated = unwrap_uses(manager.mutate_field(uses_field(&["xx"]), 2));

        assert_eq!(mutated.len(), 2);
        assert_eq!(
            mutated.iter().map(BitPattern::num_variable).sum::<usize>(),
            1
        );
        assert!(!mutated.contains(&BitPattern::parse("xx")));
    }

    #[test]
    fn mutate_field_uses_subtracts_one_point_from_four_bit_universal_cube() {
        let mut saw_subtraction = false;

        let mut manager = manager(StdRng::seed_from_u64(0));
        for seed in 0..512 {
            manager.rng = StdRng::seed_from_u64(seed);
            let mutated = unwrap_uses(manager.mutate_field(uses_field(&["xxxx"]), 4));

            if mutated.len() == 4 {
                assert_eq!(
                    mutated
                        .iter()
                        .map(|pattern| 1 << pattern.num_variable())
                        .sum::<usize>(),
                    15
                );
                assert!(!mutated.contains(&BitPattern::parse("xxxx")));
                saw_subtraction = true;
                break;
            }
        }

        assert!(
            saw_subtraction,
            "expected some seeded mutation to subtract one point from xxxx"
        );
    }

    #[test]
    fn mutate_field_uses_can_add_random_uncovered_pattern() {
        let mut added = false;

        let mut manager = manager(StdRng::seed_from_u64(0));
        for seed in 0..256 {
            manager.rng = StdRng::seed_from_u64(seed);
            let original = patterns(&["00x"]);
            let mutated = unwrap_uses(manager.mutate_field(
                FieldUses::Uses {
                    name: "field".to_string(),
                    patterns: original.clone(),
                    len: 3,
                },
                3,
            ));

            if mutated.len() > original.len() {
                let added_patterns: Vec<_> = mutated.difference(&original).collect();
                assert_eq!(added_patterns.len(), 1);
                assert_concrete(added_patterns[0]);
                assert_uncovered(added_patterns[0], &original);
                added = true;
                break;
            }
        }

        assert!(
            added,
            "expected some seeded mutation to add an uncovered pattern"
        );
    }

    #[test]
    fn mutate_field_uses_can_remove_selected_concrete_pattern() {
        let mut removed = false;

        let mut manager = manager(StdRng::seed_from_u64(0));
        for seed in 0..256 {
            manager.rng = StdRng::seed_from_u64(seed);
            let mutated = unwrap_uses(manager.mutate_field(uses_field(&["0", "1"]), 1));

            if mutated.len() == 1 {
                assert!(
                    mutated.contains(&BitPattern::parse("0"))
                        || mutated.contains(&BitPattern::parse("1"))
                );
                removed = true;
                break;
            }
        }

        assert!(
            removed,
            "expected some seeded mutation to remove a concrete pattern"
        );
    }

    #[test]
    fn mutate_field_uses_samples_existing_and_uncovered_buckets_by_frequency() {
        let mut manager = manager(StdRng::seed_from_u64(0x17));
        let field = uses_field(&["00x"]);
        let sample_count = 4_000usize;
        let expected_add_count = sample_count * 6 / 8;
        let expected_subtract_count = sample_count * 2 / 8;
        let tolerance = sample_count / 10;
        let mut add_count = 0usize;
        let mut subtract_count = 0usize;

        for _ in 0..sample_count {
            let mutated = unwrap_uses(manager.mutate_field(field.clone(), 3));
            if mutated.len() == 2 && mutated.contains(&BitPattern::parse("00x")) {
                add_count += 1;
            } else if mutated.len() == 1 && !mutated.contains(&BitPattern::parse("00x")) {
                subtract_count += 1;
            } else {
                panic!("unexpected Uses mutation outcome: {mutated:?}");
            }
        }

        assert!(
            expected_add_count.abs_diff(add_count) <= tolerance,
            "expected add count {add_count} to be within {tolerance} of {expected_add_count}"
        );
        assert!(
            expected_subtract_count.abs_diff(subtract_count) <= tolerance,
            "expected subtract count {subtract_count} to be within {tolerance} of {expected_subtract_count}"
        );
    }

    #[test]
    fn mutate_field_uses_merges_added_uncovered_pattern_with_existing_pattern() {
        let mut merged = false;

        let mut manager = manager(StdRng::seed_from_u64(0));
        for seed in 0..512 {
            manager.rng = StdRng::seed_from_u64(seed);
            let mutated = unwrap_uses(manager.mutate_field(uses_field(&["00"]), 2));

            if mutated.contains(&BitPattern::parse("0x")) {
                assert_eq!(
                    mutated,
                    patterns(&["0x"]),
                    "expected newly added adjacent pattern to merge with 00"
                );
                merged = true;
                break;
            }
        }

        assert!(
            merged,
            "expected some seeded mutation to add 01 and merge to 0x"
        );
    }

    #[test]
    fn mutate_field_uses_merges_specialized_pattern_with_neighbor() {
        let mut merged = false;

        let mut manager = manager(StdRng::seed_from_u64(0));
        for seed in 0..512 {
            manager.rng = StdRng::seed_from_u64(seed);
            let mutated = unwrap_uses(manager.mutate_field(uses_field(&["0x", "10"]), 2));

            if mutated == patterns(&["x0"]) {
                merged = true;
                break;
            }
        }

        assert!(
            merged,
            "expected some seeded mutation to specialize 0x to 00 and merge with 10 into x0"
        );
    }

    #[test]
    fn mutate_field_uses_applies_merge_until_fixed_point() {
        let mut merged_to_universal = false;

        let mut manager = manager(StdRng::seed_from_u64(0));
        for seed in 0..1024 {
            manager.rng = StdRng::seed_from_u64(seed);
            let mutated = unwrap_uses(manager.mutate_field(uses_field(&["0x", "10"]), 2));

            if mutated == patterns(&["xx"]) {
                merged_to_universal = true;
                break;
            }
        }

        assert!(
            merged_to_universal,
            "expected some seeded mutation to add 11 and merge 0x, 10, 11 into xx"
        );
    }

    #[test]
    fn construct_bitpatterns_frequencies_returns_empty_for_empty_patterns() {
        let patterns = vec![];

        assert_eq!(
            IsaOptimizationManager::<StdRng>::construct_bitpatterns_frequencies(&patterns),
            vec![]
        );
    }

    #[test]
    fn construct_bitpatterns_frequencies_counts_concrete_patterns_as_one() {
        let patterns = vec![
            BitPattern::parse("00"),
            BitPattern::parse("01"),
            BitPattern::parse("10"),
            BitPattern::parse("11"),
        ];

        assert_eq!(
            IsaOptimizationManager::<StdRng>::construct_bitpatterns_frequencies(&patterns),
            vec![1, 1, 1, 1]
        );
    }

    #[test]
    fn construct_bitpatterns_frequencies_uses_power_of_variable_bit_count() {
        let patterns = vec![
            BitPattern::parse("x"),
            BitPattern::parse("xx"),
            BitPattern::parse("x0x"),
            BitPattern::parse("xxxx"),
        ];

        assert_eq!(
            IsaOptimizationManager::<StdRng>::construct_bitpatterns_frequencies(&patterns),
            vec![2, 4, 4, 16]
        );
    }

    #[test]
    fn construct_bitpatterns_frequencies_preserves_input_order() {
        let patterns = vec![
            BitPattern::parse("xxx"),
            BitPattern::parse("0"),
            BitPattern::parse("x0"),
            BitPattern::parse("xx00x"),
        ];

        assert_eq!(
            IsaOptimizationManager::<StdRng>::construct_bitpatterns_frequencies(&patterns),
            vec![8, 1, 2, 8]
        );
    }

    #[test]
    fn construct_bitpatterns_frequencies_counts_only_var_bits() {
        let patterns = vec![
            BitPattern::new(vec![Bit::Test, Bit::Low, Bit::High]),
            BitPattern::new(vec![Bit::Var, Bit::Test, Bit::Var]),
        ];

        assert_eq!(
            IsaOptimizationManager::<StdRng>::construct_bitpatterns_frequencies(&patterns),
            vec![1, 4]
        );
    }

    #[test]
    fn random_uncovered_pattern_only_returns_concrete_uncovered_patterns() {
        let covered = patterns(&["00x", "101", "11x"]);
        let uncovered = IsaOptimizationManager::<StdRng>::uncovered_patterns(&covered, 3);
        let mut manager = manager(StdRng::seed_from_u64(0x51a0));

        for _ in 0..256 {
            let pattern = manager.random_pattern(&uncovered, 3);

            assert_concrete(&pattern);
            assert_uncovered(&pattern, &covered);
        }
    }

    #[test]
    fn random_uncovered_pattern_samples_uncovered_patterns_uniformly() {
        let covered = patterns(&["00x"]);
        let uncovered = IsaOptimizationManager::<StdRng>::uncovered_patterns(&covered, 3);
        let mut manager = manager(StdRng::seed_from_u64(0x5150));
        let sample_count = 6_000usize;
        let expected_count = sample_count / 6;
        let tolerance = expected_count / 5;
        let mut counts = HashMap::new();

        for _ in 0..sample_count {
            let pattern = manager.random_pattern(&uncovered, 3);

            assert_concrete(&pattern);
            assert_uncovered(&pattern, &covered);
            *counts.entry(pattern_string(&pattern)).or_insert(0usize) += 1;
        }

        assert_eq!(counts.len(), 6, "expected to sample all uncovered patterns");
        for pattern in ["010", "011", "100", "101", "110", "111"] {
            let count = *counts.get(pattern).unwrap_or(&0);
            assert!(
                expected_count.abs_diff(count) <= tolerance,
                "expected {pattern} count {count} to be within {tolerance} of {expected_count}"
            );
        }
    }

    #[test]
    fn random_uncovered_pattern_samples_all_patterns_when_none_are_covered() {
        let covered = patterns(&[]);
        let uncovered = IsaOptimizationManager::<StdRng>::uncovered_patterns(&covered, 2);
        let mut manager = manager(StdRng::seed_from_u64(0x0fee));
        let sample_count = 4_000usize;
        let expected_count = sample_count / 4;
        let tolerance = expected_count / 5;
        let mut counts = HashMap::new();

        for _ in 0..sample_count {
            let pattern = manager.random_pattern(&uncovered, 2);

            assert_concrete(&pattern);
            *counts.entry(pattern_string(&pattern)).or_insert(0usize) += 1;
        }

        assert_eq!(counts.len(), 4, "expected to sample all concrete patterns");
        for pattern in ["00", "01", "10", "11"] {
            let count = *counts.get(pattern).unwrap_or(&0);
            assert!(
                expected_count.abs_diff(count) <= tolerance,
                "expected {pattern} count {count} to be within {tolerance} of {expected_count}"
            );
        }
    }

    #[test]
    fn random_uncovered_pattern_handles_overlapping_covered_patterns() {
        let covered = patterns(&["0xx", "x0x", "110"]);
        let uncovered = IsaOptimizationManager::<StdRng>::uncovered_patterns(&covered, 3);
        let mut manager = manager(StdRng::seed_from_u64(0x0b1a));
        let mut sampled = HashSet::new();

        for _ in 0..256 {
            let pattern = manager.random_pattern(&uncovered, 3);

            assert_concrete(&pattern);
            assert_uncovered(&pattern, &covered);
            sampled.insert(pattern_string(&pattern));
        }

        assert_eq!(
            sampled,
            ["111".to_string()].into_iter().collect(),
            "expected only the sole uncovered pattern to be sampled"
        );
    }

    #[test]
    fn random_uncovered_pattern_repeatedly_returns_only_remaining_assignment() {
        let covered = patterns(&["0xx", "10x", "110"]);
        let uncovered = IsaOptimizationManager::<StdRng>::uncovered_patterns(&covered, 3);
        let mut manager = manager(StdRng::seed_from_u64(0x501e));

        for _ in 0..64 {
            let pattern = manager.random_pattern(&uncovered, 3);

            assert_concrete(&pattern);
            assert_eq!(pattern_string(&pattern), "111");
        }
    }
}
