use std::{
    collections::{HashMap, HashSet},
    fs,
    time::{Duration, Instant},
};

use petgraph::{
    algo::toposort,
    graph::{DiGraph, NodeIndex},
};

use crate::{
    bit::{Bit, BitPattern},
    parser::{Expr, ModuleNetlist, parse_netlist},
    stdcell_library::StandardCellLibrary,
};

type WireId = usize;

#[derive(Debug, Clone)]
enum SimInput {
    Wire(WireId),
    Const(Bit),
}

#[derive(Debug, Clone)]
struct CompiledOutput {
    wire_name: String,
    function: crate::bit::LookupTable,
    alias_wires: Vec<WireId>,
}

#[derive(Debug, Clone)]
struct CompiledGate {
    instance_name: String,
    inputs: Vec<SimInput>,

    outputs: Vec<CompiledOutput>,
    output_alias_wires: Vec<WireId>,
}

#[derive(Debug)]
struct StampedWireValues {
    values: Vec<Bit>,
    stamps: Vec<u32>,
    generation: u32,
}

impl StampedWireValues {
    fn new(wire_count: usize) -> Self {
        Self {
            values: vec![Bit::Low; wire_count],
            stamps: vec![0; wire_count],
            generation: 1,
        }
    }

    fn reset(&mut self, wire_count: usize) {
        if self.values.len() != wire_count {
            self.values.resize(wire_count, Bit::Low);
            self.stamps.resize(wire_count, 0);
        }

        self.generation = self.generation.wrapping_add(1);
        if self.generation == 0 {
            self.stamps.fill(0);
            self.generation = 1;
        }
    }

    fn write(&mut self, wire_id: WireId, value: Bit) {
        self.values[wire_id] = value;
        self.stamps[wire_id] = self.generation;
    }

    fn read(&self, wire_id: WireId) -> Option<Bit> {
        (self.stamps[wire_id] == self.generation).then_some(self.values[wire_id])
    }
}

#[derive(Debug)]
pub struct Simulator {
    top_mod_output_wire_ids: Vec<WireId>,

    // Compiled simulation fields using node indices
    // compiled_gates is sorted by the topological sort order of the digraph
    input_wire_names: Vec<String>,
    wire_ids: HashMap<String, WireId>,
    wire_names: Vec<String>,
    alias_wire_ids: Vec<Vec<WireId>>,
    compiled_gates: Vec<CompiledGate>,

    sequential_output_wires: Vec<WireId>,
    sequential_input_wires: Vec<WireId>,
    constant_writes: Vec<(WireId, Bit)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateOutputAssignment {
    pub wire_name: String,
    pub value: Bit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateUsageOptimization {
    pub gates_to_comment: Vec<String>,
    pub assignments: Vec<GateOutputAssignment>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptimizationValidation {
    pub input_patterns_checked: usize,
    pub effective_outputs_checked: usize,
    pub replacement_outputs_checked: usize,
    pub gate_evaluations: usize,
    pub elapsed: Duration,
}

#[derive(Debug, Clone)]
pub struct CompiledOptimizationInputs {
    // Each optimization input pattern after translating net names to dense wire ids. This avoids
    // doing string/hash lookups every time we simulate the same pattern set.
    inputs: Vec<Vec<(WireId, Bit)>>,
}

#[derive(Debug, Clone, Copy)]
struct StaticOutputRef {
    gate_idx: usize,
    output_idx: usize,
    wire_id: WireId,
}

#[derive(Debug)]
pub struct OptimizationWorkspace {
    // Reused full-circuit wire values for one simulated input pattern. This is cleared between
    // patterns, but the allocation is kept.
    wires: Vec<Option<Bit>>,

    // Generation-stamped wire values for the optimization hot path. Resetting this for each input
    // pattern only increments a generation counter instead of clearing every wire.
    stamped_wires: StampedWireValues,

    // For each gate output, the concrete value seen so far if that output is still possibly
    // static. `None` means either no pattern has been processed yet for that output, or the shape
    // has just been reset.
    static_output_values: Vec<Vec<Option<Bit>>>,

    // For each gate output, true until we observe either Bit::Var/Bit::Test or a concrete value
    // different from `static_output_values`.
    output_is_static: Vec<Vec<bool>>,

    // Flat list of outputs still worth checking for staticness. Outputs are removed as soon as
    // they become non-static, avoiding repeated scans of already-dead outputs.
    live_static_outputs: Vec<StaticOutputRef>,
}

impl OptimizationWorkspace {
    fn new(wire_count: usize, gates: &[CompiledGate]) -> Self {
        Self {
            wires: vec![None; wire_count],
            stamped_wires: StampedWireValues::new(wire_count),
            static_output_values: gates
                .iter()
                .map(|gate| vec![None; gate.outputs.len()])
                .collect(),
            output_is_static: gates
                .iter()
                .map(|gate| vec![true; gate.outputs.len()])
                .collect(),
            live_static_outputs: Vec::new(),
        }
    }

    fn reset_for(&mut self, wire_count: usize, gates: &[CompiledGate]) {
        // Called once at the start of a complete optimization run. It clears all results that must
        // be accumulated over the whole input-pattern set while retaining allocations.
        self.reset_wires(wire_count);
        self.stamped_wires.reset(wire_count);

        resize_gate_output_bits(&mut self.static_output_values, gates, None);
        resize_gate_output_bits(&mut self.output_is_static, gates, true);
        self.live_static_outputs.clear();
        self.live_static_outputs
            .extend(gates.iter().enumerate().flat_map(|(gate_idx, gate)| {
                gate.outputs
                    .iter()
                    .enumerate()
                    .map(move |(output_idx, output)| StaticOutputRef {
                        gate_idx,
                        output_idx,
                        wire_id: output.alias_wires[0],
                    })
            }));
    }

    fn reset_wires(&mut self, wire_count: usize) {
        // Called for each input pattern. Wire values are pattern-specific, so these cannot be
        // preserved across simulations.
        self.wires.clear();
        self.wires.resize(wire_count, None);
    }
}

fn resize_gate_output_bits<T: Copy>(
    values: &mut Vec<Vec<T>>,
    gates: &[CompiledGate],
    default_value: T,
) {
    values.resize_with(gates.len(), Vec::new);

    for (gate_idx, gate) in gates.iter().enumerate() {
        values[gate_idx].clear();
        values[gate_idx].resize(gate.outputs.len(), default_value);
    }
}

impl Simulator {
    pub fn from_file(netlist_file: &str, standard_cell_file: &str) -> Self {
        let verilog = fs::read_to_string(netlist_file).unwrap();
        let netlist = parse_netlist(&verilog).unwrap();
        let cell_library = StandardCellLibrary::new(standard_cell_file).unwrap();

        let alias_map = build_alias_map(&netlist);
        let top_mod_outputs = compute_top_mod_outputs(&netlist, &cell_library, &alias_map);

        validate_instances(&netlist, &cell_library);

        let graph = build_dependency_graph(&netlist, &cell_library, &alias_map);
        let gate_sorted_order = sorted_gate_order(&graph);

        let (wire_ids, wire_names) = compile_wire_ids(&netlist);
        let alias_wire_ids = compile_alias_wire_ids(&alias_map, &wire_ids, wire_names.len());
        let top_mod_output_wire_ids = top_mod_outputs
            .iter()
            .filter_map(|wire_name| wire_ids.get(wire_name).copied())
            .collect();

        let (sequential_output_wires, sequential_input_wires) =
            compile_sequential_io(&netlist, &cell_library, &wire_ids);

        let constant_writes = compile_constant_writes(&alias_map, &wire_ids);

        let compiled_gates = compile_gates(
            &netlist,
            &cell_library,
            &graph,
            &gate_sorted_order,
            &wire_ids,
            &alias_wire_ids,
        );

        Self {
            top_mod_output_wire_ids,
            input_wire_names: netlist.inputs,
            wire_ids,
            wire_names,
            alias_wire_ids,
            compiled_gates,

            sequential_output_wires,
            sequential_input_wires,
            constant_writes,
        }
    }

    pub fn input_wire_names(&self) -> &[String] {
        &self.input_wire_names
    }

    pub fn pattern_to_sim_inputs(
        &self,
        pattern: &BitPattern,
        instruction_input_name: &str,
    ) -> HashMap<String, Bit> {
        let mut sim_inputs = HashMap::new();
        let indexed_prefix = format!("{}[", instruction_input_name);
        let mut saw_instruction_input = false;

        for input in &self.input_wire_names {
            if let Some(inst_idx) = input
                .strip_prefix(&indexed_prefix)
                .and_then(|rest| rest.strip_suffix("]"))
                .and_then(|idx| idx.parse::<usize>().ok())
            {
                assert!(
                    inst_idx < pattern.bits.len(),
                    "Instruction input {} is outside the {}-bit pattern",
                    input,
                    pattern.bits.len()
                );
                sim_inputs.insert(
                    input.clone(),
                    pattern.bits[pattern.bits.len() - 1 - inst_idx],
                );
                saw_instruction_input = true;
            } else {
                sim_inputs.insert(input.clone(), Bit::Var);
            }
        }

        assert!(
            saw_instruction_input,
            "No primary inputs matched instruction input {}",
            instruction_input_name
        );

        sim_inputs
    }

    pub fn optimization_workspace(&self) -> OptimizationWorkspace {
        OptimizationWorkspace::new(self.wire_names.len(), &self.compiled_gates)
    }

    /// Replaces gates whose every output is globally constant over the supplied abstract input
    /// patterns. Effective outputs include both module-level outputs and inputs to sequential
    /// gates, since sequential inputs carry information into future cycles.
    ///
    /// `Bit::Var` inputs conservatively stand for both Boolean values. Therefore a concrete
    /// low/high result proves that output has the same value for every represented concrete input.
    /// Gates that are merely unobservable or constant only while observable are retained because
    /// independently valid don't-care substitutions need not remain valid when applied together.
    ///
    /// # Arguments
    /// * `bit_inputs` - A list of inputs to the module to test
    ///
    /// # Returns
    /// * `Vec<String>` - A list of all retained combinational gate instance names
    pub fn optimize_gate_usage(&self, bit_inputs: &Vec<HashMap<String, Bit>>) -> Vec<String> {
        let optimization = self.optimize_gate_usage_details(bit_inputs);
        self.retained_gate_names(&optimization)
    }

    pub fn combinational_gate_count(&self) -> usize {
        self.compiled_gates.len()
    }

    pub fn optimize_gate_usage_details(
        &self,
        bit_inputs: &Vec<HashMap<String, Bit>>,
    ) -> GateUsageOptimization {
        // Convenience path for one-off calls. Repeated callers should keep this workspace around
        // and call `optimize_gate_usage_details_with_workspace` to avoid reallocating buffers.
        let mut workspace = self.optimization_workspace();
        self.optimize_gate_usage_details_with_workspace(bit_inputs, &mut workspace)
    }

    pub fn optimize_gate_usage_details_batch(
        &self,
        bit_input_sets: &[Vec<HashMap<String, Bit>>],
    ) -> Vec<GateUsageOptimization> {
        // One workspace is reused for the whole batch. Each individual optimization run still
        // clears its accumulated results via `reset_for`.
        let mut workspace = self.optimization_workspace();

        bit_input_sets
            .iter()
            .map(|bit_inputs| {
                self.optimize_gate_usage_details_with_workspace(bit_inputs, &mut workspace)
            })
            .collect()
    }

    pub fn optimize_gate_usage_details_with_workspace(
        &self,
        bit_inputs: &Vec<HashMap<String, Bit>>,
        workspace: &mut OptimizationWorkspace,
    ) -> GateUsageOptimization {
        // Translate input net names to wire ids once for this call. If the same bit_inputs are
        // reused across many calls, use `compile_optimization_inputs` directly and pass the result
        // to `optimize_compiled_gate_usage_details_with_workspace`.
        let compiled_bit_inputs = self.compile_optimization_inputs(bit_inputs);
        self.optimize_compiled_gate_usage_details_with_workspace(&compiled_bit_inputs, workspace)
    }

    pub fn optimize_compiled_gate_usage_details_with_workspace(
        &self,
        bit_inputs: &CompiledOptimizationInputs,
        workspace: &mut OptimizationWorkspace,
    ) -> GateUsageOptimization {
        let indices =
            self.optimize_compiled_removable_gate_indices_with_workspace(bit_inputs, workspace);

        // self.run_compiled_gate_usage_optimization(bit_inputs, workspace);

        let mut gates_to_comment = Vec::new();
        let mut assignments = Vec::new();
        for gate_idx in indices {
            let gate = &self.compiled_gates[gate_idx];
            gates_to_comment.push(gate.instance_name.clone());
            for (out_idx, output) in gate.outputs.iter().enumerate() {
                if workspace.output_is_static[gate_idx][out_idx] {
                    assignments.push(GateOutputAssignment {
                        wire_name: output.wire_name.clone(),
                        value: workspace.static_output_values[gate_idx][out_idx]
                            .expect("Output is static, it should have a static value"),
                    })
                } else {
                    // Otherwise, this was removed because it is unobservable because its output is
                    // only the input to a gate which is already being removed
                    // Thus, it doesn't matter which value we give it
                    assignments.push(GateOutputAssignment {
                        wire_name: output.wire_name.clone(),
                        value: Bit::Low,
                    })
                }
            }
        }
        // for (gate_idx, gate) in self.compiled_gates.iter().enumerate() {
        //     // If any item in the iterator of Option<Bit>s is None, this static_values will resolve
        //     // to None. Otherwise (if there is a static value for every gate) it will be Some.
        //     let static_values: Option<Vec<Bit>> = gate
        //         .outputs
        //         .iter()
        //         .enumerate()
        //         .map(|(output_idx, _)| {
        //             workspace.output_is_static[gate_idx][output_idx]
        //                 .then_some(workspace.static_output_values[gate_idx][output_idx])
        //                 .flatten()
        //         })
        //         .collect();

        //     if let Some(values) = static_values {
        //         gates_to_comment.push(gate.instance_name.clone());

        //         for (output, value) in gate.outputs.iter().zip(values) {
        //             assignments.push(GateOutputAssignment {
        //                 wire_name: output.wire_name.clone(),
        //                 value,
        //             });
        //         }
        //     }
        // }

        GateUsageOptimization {
            gates_to_comment,
            assignments,
        }
    }

    pub fn optimize_compiled_gate_usage_count_with_workspace(
        &self,
        bit_inputs: &CompiledOptimizationInputs,
        workspace: &mut OptimizationWorkspace,
    ) -> usize {
        self.optimize_compiled_removable_gate_indices_with_workspace(bit_inputs, workspace)
            .len()
    }

    fn optimize_compiled_removable_gate_indices_with_workspace(
        &self,
        bit_inputs: &CompiledOptimizationInputs,
        workspace: &mut OptimizationWorkspace,
    ) -> Vec<usize> {
        self.run_compiled_gate_usage_optimization(bit_inputs, workspace);
        let static_gates = self.optimize_compiled_static_gate_indices_with_workspace(workspace);
        let unobservable_gates =
            self.optimize_compiled_unobservable_indices_with_workspace(workspace, &static_gates);
        static_gates
            .into_iter()
            .chain(unobservable_gates.into_iter())
            .collect()
    }

    /// Identifies, given a workspace which has already been simulated, all gates which have static
    /// values for all inputs
    fn optimize_compiled_static_gate_indices_with_workspace(
        &self,
        workspace: &mut OptimizationWorkspace,
    ) -> Vec<usize> {
        let mut gates_to_comment = Vec::new();

        for (gate_idx, gate) in self.compiled_gates.iter().enumerate() {
            // If any item in the iterator of Option<Bit>s is None, this static_values will resolve
            // to None. Otherwise (if there is a static value for every gate) it will be Some.
            let static_values: Option<Vec<Bit>> = gate
                .outputs
                .iter()
                .enumerate()
                .map(|(output_idx, _)| {
                    workspace.output_is_static[gate_idx][output_idx]
                        .then_some(workspace.static_output_values[gate_idx][output_idx])
                        .flatten()
                })
                .collect();

            if let Some(_) = static_values {
                gates_to_comment.push(gate_idx);
            }
        }

        gates_to_comment
    }

    /// Identifies, given a simulated workspace and a list of gates which are already being removed,
    /// a list of gates which now no longer exist in the output path.
    /// Done using backwards traversal from the outputs, checking to see which gates have no paths
    /// to the output which don't go through a removed_gate_indices item
    fn optimize_compiled_unobservable_indices_with_workspace(
        &self,
        _workspace: &mut OptimizationWorkspace,
        removed_gates_indices: &Vec<usize>,
    ) -> Vec<usize> {
        let mut removed = vec![false; self.compiled_gates.len()];
        // Wires in `needed` have a path to an effective output that does not cross a removed gate.
        let mut needed = vec![false; self.wire_names.len()];
        // Wires in `cut_only` are used by removed/unobservable gates, but have not been proven
        // needed by an intact output path.
        let mut cut_only = vec![false; self.wire_names.len()];
        let mut gates_to_comment = Vec::new();

        for &gate_idx in removed_gates_indices {
            removed[gate_idx] = true;
        }
        for &wire_id in &self.top_mod_output_wire_ids {
            needed[wire_id] = true;
        }

        for (gate_idx, gate) in self.compiled_gates.iter().enumerate().rev() {
            if removed[gate_idx] {
                // Removed gates cut observability for their inputs unless another later gate marks
                // those same wires as `needed`.
                for input in &gate.inputs {
                    if let SimInput::Wire(wire_id) = *input {
                        set_wire_and_aliases(&mut cut_only, wire_id, &self.alias_wire_ids);
                    }
                }
                continue;
            }

            let output_needed = gate
                .output_alias_wires
                .iter()
                .any(|&wire_id| wire_or_alias_is_marked(&needed, wire_id, &self.alias_wire_ids));
            if output_needed {
                // This gate is still observable, so its wire inputs are also required.
                for input in &gate.inputs {
                    if let SimInput::Wire(wire_id) = *input {
                        set_wire_and_aliases(&mut needed, wire_id, &self.alias_wire_ids);
                    }
                }
            } else if gate
                .output_alias_wires
                .iter()
                .any(|&wire_id| wire_or_alias_is_marked(&cut_only, wire_id, &self.alias_wire_ids))
            {
                // The output is only demanded across a cut, so replacing it cannot affect any
                // effective output. Its own inputs become cut-only candidates too.
                gates_to_comment.push(gate_idx);
                for input in &gate.inputs {
                    if let SimInput::Wire(wire_id) = *input {
                        set_wire_and_aliases(&mut cut_only, wire_id, &self.alias_wire_ids);
                    }
                }
            }
        }

        gates_to_comment
    }

    fn run_compiled_gate_usage_optimization(
        &self,
        bit_inputs: &CompiledOptimizationInputs,
        workspace: &mut OptimizationWorkspace,
    ) {
        // Clear all state accumulated over an optimization run. The vectors keep their allocations
        // so repeated runs stay cheap.
        workspace.reset_for(self.wire_names.len(), &self.compiled_gates);

        for bit_input in &bit_inputs.inputs {
            // Each input pattern needs a fresh simulated wire state. Static-output tracking
            // intentionally persists across every pattern in this optimization run.
            workspace.stamped_wires.reset(self.wire_names.len());
            self.apply_primary_wire_inputs_stamped(bit_input, &mut workspace.stamped_wires);
            self.apply_sequential_outputs_stamped(&mut workspace.stamped_wires);
            self.apply_constant_assigns_stamped(&mut workspace.stamped_wires);
            self.simulate_compiled_gates_range_stamped(
                &mut workspace.stamped_wires,
                0,
                self.compiled_gates.len(),
            );

            // DEBUG: every wire produced by a compiled gate, plus every effective output, should
            // have a value after a full simulation. If this fails, the netlist was not fully
            // simulated for this input pattern.
            debug_assert!(
                self.compiled_gates
                    .iter()
                    .flat_map(|gate| gate.output_alias_wires.iter())
                    .chain(self.top_mod_output_wire_ids.iter())
                    .all(|wire_id| workspace.stamped_wires.read(*wire_id).is_some())
            );

            // Track outputs that are constant over every supplied input pattern. Only concrete
            // low/high values count as static; Bit::Var means the value still depends on an
            // unconstrained input, so assigning a constant would be unsound.
            let mut idx = 0;
            while idx < workspace.live_static_outputs.len() {
                let output = workspace.live_static_outputs[idx];
                let value = workspace
                    .stamped_wires
                    .read(output.wire_id)
                    .expect("gate output should be simulated");

                let became_non_static = if !matches!(value, Bit::Low | Bit::High) {
                    true
                } else {
                    match workspace.static_output_values[output.gate_idx][output.output_idx] {
                        Some(prev) => prev != value,
                        None => {
                            workspace.static_output_values[output.gate_idx][output.output_idx] =
                                Some(value);
                            false
                        }
                    }
                };

                if became_non_static {
                    workspace.output_is_static[output.gate_idx][output.output_idx] = false;
                    workspace.live_static_outputs.swap_remove(idx);
                } else {
                    idx += 1;
                }
            }
        }
    }

    fn retained_gate_names(&self, optimization: &GateUsageOptimization) -> Vec<String> {
        let gates_to_comment: HashSet<&str> = optimization
            .gates_to_comment
            .iter()
            .map(String::as_str)
            .collect();

        self.compiled_gates
            .iter()
            .filter(|gate| !gates_to_comment.contains(gate.instance_name.as_str()))
            .map(|gate| gate.instance_name.clone())
            .collect()
    }

    /// Validates an optimization returned by `optimize_compiled_gate_usage_details_with_workspace`.
    ///
    /// This is intentionally separate from optimization so callers that do not need the additional
    /// full-circuit simulations pay no validation cost.
    pub fn validate_compiled_gate_usage_optimization_with_workspace(
        &self,
        bit_inputs: &CompiledOptimizationInputs,
        optimization: &GateUsageOptimization,
        workspace: &mut OptimizationWorkspace,
    ) -> OptimizationValidation {
        let validation_started = Instant::now();
        let replacement_values = self.compile_optimization_replacements(optimization);

        let mut effective_outputs_checked = 0;
        let mut replacement_outputs_checked = 0;
        let mut gate_evaluations = 0;
        let mut optimized_wires = vec![None; self.wire_names.len()];

        for (pattern_idx, bit_input) in bit_inputs.inputs.iter().enumerate() {
            workspace.reset_wires(self.wire_names.len());
            optimized_wires.fill(None);

            self.apply_primary_wire_inputs(bit_input, &mut workspace.wires);
            self.apply_sequential_outputs(&mut workspace.wires);
            self.apply_constant_assigns(&mut workspace.wires);

            self.apply_primary_wire_inputs(bit_input, &mut optimized_wires);
            self.apply_sequential_outputs(&mut optimized_wires);
            self.apply_constant_assigns(&mut optimized_wires);

            self.simulate_compiled_gates_range(&mut workspace.wires, 0, self.compiled_gates.len());
            gate_evaluations += self.compiled_gates.len();

            gate_evaluations += self.simulate_compiled_gates_with_replacements(
                &mut optimized_wires,
                &replacement_values,
            );

            for (gate_idx, values) in replacement_values.iter().enumerate() {
                let Some(values) = values else {
                    continue;
                };
                let gate = &self.compiled_gates[gate_idx];
                assert_eq!(values.len(), gate.outputs.len());

                for (output, &replacement) in gate.outputs.iter().zip(values) {
                    assert!(
                        matches!(replacement, Bit::Low | Bit::High),
                        "replacement for {}.{} is not a constant",
                        gate.instance_name,
                        output.wire_name,
                    );

                    let original = workspace.wires[output.alias_wires[0]]
                        .expect("replaced gate output was not simulated");
                    assert_eq!(
                        original, replacement,
                        "post-optimization validation rejected {}.{} for input pattern {}",
                        gate.instance_name, output.wire_name, pattern_idx,
                    );
                    replacement_outputs_checked += 1;
                }
            }

            for &wire_id in &self.top_mod_output_wire_ids {
                let original =
                    workspace.wires[wire_id].expect("effective output was not simulated");
                let optimized =
                    optimized_wires[wire_id].expect("optimized effective output was not simulated");
                assert_eq!(
                    original, optimized,
                    "post-optimization validation changed effective output {} for input pattern {}",
                    self.wire_names[wire_id], pattern_idx,
                );
                effective_outputs_checked += 1;
            }
        }

        OptimizationValidation {
            input_patterns_checked: bit_inputs.inputs.len(),
            effective_outputs_checked,
            replacement_outputs_checked,
            gate_evaluations,
            elapsed: validation_started.elapsed(),
        }
    }

    pub fn validate_gate_usage_optimization(
        &self,
        bit_inputs: &Vec<HashMap<String, Bit>>,
        optimization: &GateUsageOptimization,
    ) -> OptimizationValidation {
        let compiled_bit_inputs = self.compile_optimization_inputs(bit_inputs);
        let mut workspace = self.optimization_workspace();
        self.validate_compiled_gate_usage_optimization_with_workspace(
            &compiled_bit_inputs,
            optimization,
            &mut workspace,
        )
    }

    fn compile_optimization_replacements(
        &self,
        optimization: &GateUsageOptimization,
    ) -> Vec<Option<Vec<Bit>>> {
        let assignments: HashMap<&str, Bit> = optimization
            .assignments
            .iter()
            .map(|assignment| (assignment.wire_name.as_str(), assignment.value))
            .collect();
        assert_eq!(
            assignments.len(),
            optimization.assignments.len(),
            "optimization contains duplicate output assignments",
        );
        let gates_to_comment: HashSet<&str> = optimization
            .gates_to_comment
            .iter()
            .map(String::as_str)
            .collect();

        let replacement_values: Vec<Option<Vec<Bit>>> = self
            .compiled_gates
            .iter()
            .map(|gate| {
                if !gates_to_comment.contains(gate.instance_name.as_str()) {
                    return None;
                }

                Some(
                    gate.outputs
                        .iter()
                        .map(|output| {
                            *assignments
                                .get(output.wire_name.as_str())
                                .unwrap_or_else(|| {
                                    panic!(
                                        "commented gate {} has no replacement for output {}",
                                        gate.instance_name, output.wire_name,
                                    )
                                })
                        })
                        .collect(),
                )
            })
            .collect();
        let replacement_gate_count = replacement_values
            .iter()
            .filter(|values| values.is_some())
            .count();
        let replacement_output_count = replacement_values
            .iter()
            .flatten()
            .map(Vec::len)
            .sum::<usize>();

        assert_eq!(
            replacement_gate_count,
            gates_to_comment.len(),
            "optimization references an unknown gate",
        );
        assert_eq!(
            replacement_output_count,
            assignments.len(),
            "optimization contains an assignment that does not replace a commented gate output",
        );

        replacement_values
    }

    fn simulate_compiled_gates_with_replacements(
        &self,
        wires: &mut [Option<Bit>],
        replacement_values: &[Option<Vec<Bit>>],
    ) -> usize {
        let mut input_values = Vec::new();
        let mut gate_evaluations = 0;

        for (gate_idx, gate) in self.compiled_gates.iter().enumerate() {
            if let Some(values) = &replacement_values[gate_idx] {
                assert_eq!(values.len(), gate.outputs.len());

                for (output, &value) in gate.outputs.iter().zip(values) {
                    for &wire_id in &output.alias_wires {
                        wires[wire_id] = Some(value);
                    }
                }
                continue;
            }

            input_values.clear();
            for input in &gate.inputs {
                let value = read_sim_input(wires, input)
                    .unwrap_or_else(|| panic!("No simulated value for input {:?}", input));
                input_values.push(value);
            }

            for output in &gate.outputs {
                let value = output.function.evaluate(&input_values);
                for &wire_id in &output.alias_wires {
                    wires[wire_id] = Some(value);
                }
            }
            gate_evaluations += 1;
        }

        gate_evaluations
    }

    /// Simulates the module from a certain `start_idx` in `compiled_gates` to an `end_idx` (exclusive)
    /// All `wires` before `start_idx` must be Some(Bit).
    fn simulate_compiled_gates_range(
        &self,
        wires: &mut Vec<Option<Bit>>,
        start_idx: usize,
        end_idx: usize,
    ) {
        let mut input_values = Vec::new();

        for idx in start_idx..end_idx {
            let gate = &self.compiled_gates[idx];
            input_values.clear();

            for input in &gate.inputs {
                let value = read_sim_input(wires, input)
                    .unwrap_or_else(|| panic!("No simulated value for input {:?}", input));

                input_values.push(value);
            }

            for output in &gate.outputs {
                let value = output.function.evaluate(&input_values);

                for &wire_id in &output.alias_wires {
                    wires[wire_id] = Some(value);
                }
            }
        }
    }

    fn simulate_compiled_gates_range_stamped(
        &self,
        wires: &mut StampedWireValues,
        start_idx: usize,
        end_idx: usize,
    ) {
        for idx in start_idx..end_idx {
            let gate = &self.compiled_gates[idx];

            for output in &gate.outputs {
                let value = evaluate_lookup_table_with_stamped_inputs(
                    &output.function,
                    wires,
                    &gate.inputs,
                );

                for &wire_id in &output.alias_wires {
                    wires.write(wire_id, value);
                }
            }
        }
    }

    /// Takes, as input, the values of all the inputs for a module `bit_input` and an existing set of wires_nonarbitrary
    /// Outputs a hashmap of the values of every wire after simulation, as well as a HashSet of all
    /// wires which impact the outputs of at least one gate (ie wires whose values, if changed, would impact the circuit)
    pub fn simulate(
        &self,
        bit_input: &HashMap<String, Bit>,
        wires_nonarbitrary: &mut HashSet<WireId>,
    ) -> HashMap<String, Bit> {
        let mut wires: Vec<Option<Bit>> = vec![None; self.wire_names.len()];

        self.apply_primary_inputs(bit_input, &mut wires);
        self.apply_sequential_outputs(&mut wires);
        self.mark_sequential_inputs_nonarbitrary(wires_nonarbitrary);
        self.apply_constant_assigns(&mut wires);

        self.simulate_compiled_gates(&mut wires, wires_nonarbitrary);

        self.export_wires(&wires)
    }

    fn simulate_compiled_gates(
        &self,
        wires: &mut [Option<Bit>],
        wires_nonarbitrary: &mut HashSet<WireId>,
    ) {
        let mut input_values = Vec::new();

        for gate in &self.compiled_gates {
            input_values.clear();

            for input in &gate.inputs {
                let value = read_sim_input(wires, input)
                    .unwrap_or_else(|| panic!("No simulated value for input {:?}", input));

                input_values.push(value);
            }

            for output in &gate.outputs {
                let value = output.function.evaluate(&input_values);

                for &wire_id in &output.alias_wires {
                    wires[wire_id] = Some(value);
                }
            }

            self.mark_gate_sensitive_inputs(gate, &mut input_values, wires_nonarbitrary);
        }
    }

    fn apply_primary_inputs(&self, bit_input: &HashMap<String, Bit>, wires: &mut [Option<Bit>]) {
        for (net_name, value) in bit_input {
            let wire_id = *self
                .wire_ids
                .get(net_name)
                .unwrap_or_else(|| panic!("Unknown primary input net {}", net_name));

            write_wire_id_with_aliases(wires, &self.alias_wire_ids, wire_id, *value);
        }
    }

    pub fn compile_optimization_inputs(
        &self,
        bit_inputs: &Vec<HashMap<String, Bit>>,
    ) -> CompiledOptimizationInputs {
        let inputs = bit_inputs
            .iter()
            .map(|bit_input| {
                bit_input
                    .iter()
                    .map(|(net_name, value)| {
                        let wire_id = *self
                            .wire_ids
                            .get(net_name)
                            .unwrap_or_else(|| panic!("Unknown primary input net {}", net_name));

                        (wire_id, *value)
                    })
                    .collect()
            })
            .collect();

        CompiledOptimizationInputs { inputs }
    }

    fn apply_primary_wire_inputs(&self, bit_input: &[(WireId, Bit)], wires: &mut [Option<Bit>]) {
        for &(wire_id, value) in bit_input {
            write_wire_id_with_aliases(wires, &self.alias_wire_ids, wire_id, value);
        }
    }

    fn apply_primary_wire_inputs_stamped(
        &self,
        bit_input: &[(WireId, Bit)],
        wires: &mut StampedWireValues,
    ) {
        for &(wire_id, value) in bit_input {
            write_wire_id_with_aliases_stamped(wires, &self.alias_wire_ids, wire_id, value);
        }
    }

    fn apply_sequential_outputs(&self, wires: &mut [Option<Bit>]) {
        for &wire_id in &self.sequential_output_wires {
            write_wire_id_with_aliases(wires, &self.alias_wire_ids, wire_id, Bit::Var);
        }
    }

    fn apply_sequential_outputs_stamped(&self, wires: &mut StampedWireValues) {
        for &wire_id in &self.sequential_output_wires {
            write_wire_id_with_aliases_stamped(wires, &self.alias_wire_ids, wire_id, Bit::Var);
        }
    }

    fn mark_sequential_inputs_nonarbitrary(&self, wires_nonarbitrary: &mut HashSet<WireId>) {
        for &wire_id in &self.sequential_input_wires {
            self.mark_wire_and_aliases_nonarbitrary(wire_id, wires_nonarbitrary);
        }
    }

    fn apply_constant_assigns(&self, wires: &mut [Option<Bit>]) {
        for &(wire_id, value) in &self.constant_writes {
            write_wire_id_with_aliases(wires, &self.alias_wire_ids, wire_id, value);
        }
    }

    fn apply_constant_assigns_stamped(&self, wires: &mut StampedWireValues) {
        for &(wire_id, value) in &self.constant_writes {
            write_wire_id_with_aliases_stamped(wires, &self.alias_wire_ids, wire_id, value);
        }
    }

    fn mark_gate_sensitive_inputs(
        &self,
        gate: &CompiledGate,
        input_values: &mut Vec<Bit>,
        wires_nonarbitrary: &mut HashSet<WireId>,
    ) {
        for input_idx in 0..gate.inputs.len() {
            let SimInput::Wire(wire_id) = gate.inputs[input_idx] else {
                continue;
            };

            if self.wire_or_alias_is_nonarbitrary(wire_id, wires_nonarbitrary) {
                continue;
            }

            let old_value = std::mem::replace(&mut input_values[input_idx], Bit::Test);

            let is_sensitive = gate
                .outputs
                .iter()
                .any(|output| output.function.evaluate(input_values) == Bit::Test);

            input_values[input_idx] = old_value;

            if is_sensitive {
                self.mark_wire_and_aliases_nonarbitrary(wire_id, wires_nonarbitrary);
            }
        }
    }

    fn wire_or_alias_is_nonarbitrary(
        &self,
        wire_id: WireId,
        wires_nonarbitrary: &HashSet<WireId>,
    ) -> bool {
        wires_nonarbitrary.contains(&wire_id)
            || self.alias_wire_ids[wire_id]
                .iter()
                .any(|alias_id| wires_nonarbitrary.contains(alias_id))
    }

    fn mark_wire_and_aliases_nonarbitrary(
        &self,
        wire_id: WireId,
        wires_nonarbitrary: &mut HashSet<WireId>,
    ) {
        wires_nonarbitrary.insert(wire_id);

        for &alias_id in &self.alias_wire_ids[wire_id] {
            wires_nonarbitrary.insert(alias_id);
        }
    }

    pub fn export_nonarbitrary_wires(&self, wires_nonarbitrary: &HashSet<WireId>) -> HashSet<Expr> {
        wires_nonarbitrary
            .iter()
            .map(|&wire_id| Expr::Net(self.wire_names[wire_id].clone()))
            .collect()
    }

    fn export_wires(&self, wires: &[Option<Bit>]) -> HashMap<String, Bit> {
        let mut result = HashMap::with_capacity(self.wire_names.len());

        for (wire_id, maybe_value) in wires.iter().enumerate() {
            if let Some(value) = maybe_value {
                result.insert(self.wire_names[wire_id].clone(), *value);
            }
        }

        result
    }
}

fn write_wire_id_with_aliases(
    wires: &mut [Option<Bit>],
    alias_wire_ids: &[Vec<WireId>],
    wire_id: WireId,
    value: Bit,
) {
    for alias_id in &alias_wire_ids[wire_id] {
        wires[*alias_id] = Some(value);
    }
}

fn write_wire_id_with_aliases_stamped(
    wires: &mut StampedWireValues,
    alias_wire_ids: &[Vec<WireId>],
    wire_id: WireId,
    value: Bit,
) {
    for &alias_id in &alias_wire_ids[wire_id] {
        wires.write(alias_id, value);
    }
}

fn wire_or_alias_is_marked(
    marked: &[bool],
    wire_id: WireId,
    alias_wire_ids: &[Vec<WireId>],
) -> bool {
    marked[wire_id]
        || alias_wire_ids[wire_id]
            .iter()
            .any(|&alias_id| marked[alias_id])
}

fn set_wire_and_aliases(marked: &mut [bool], wire_id: WireId, alias_wire_ids: &[Vec<WireId>]) {
    marked[wire_id] = true;
    for &alias_id in &alias_wire_ids[wire_id] {
        marked[alias_id] = true;
    }
}

fn read_sim_input(wires: &[Option<Bit>], input: &SimInput) -> Option<Bit> {
    match input {
        SimInput::Wire(id) => wires[*id],
        SimInput::Const(bit) => Some(*bit),
    }
}

fn read_sim_input_stamped(wires: &StampedWireValues, input: &SimInput) -> Option<Bit> {
    match input {
        SimInput::Wire(id) => wires.read(*id),
        SimInput::Const(bit) => Some(*bit),
    }
}

fn evaluate_lookup_table_with_stamped_inputs(
    table: &crate::bit::LookupTable,
    wires: &StampedWireValues,
    inputs: &[SimInput],
) -> Bit {
    table.evaluate_iter(inputs.iter().map(|input| {
        read_sim_input_stamped(wires, input)
            .unwrap_or_else(|| panic!("No simulated value for input {:?}", input))
    }))
}

fn build_alias_map(netlist: &ModuleNetlist) -> HashMap<Expr, HashSet<String>> {
    let mut alias_map = HashMap::new();

    // Create trivial aliases (wire = wire)
    for wire in netlist.all_declared_nets() {
        alias_map.insert(Expr::Net(wire.clone()), HashSet::from([wire.clone()]));
    }

    // Create single level assign aliases
    for assignment in netlist.assignments.iter() {
        if let Some(value) = alias_map.get_mut(&assignment.rhs) {
            if let Expr::Net(net_name) = &assignment.lhs {
                value.insert(net_name.clone());
            }
        } else {
            if let Expr::Net(net_name) = &assignment.lhs {
                alias_map.insert(assignment.rhs.clone(), HashSet::from([net_name.clone()]));
            }
        }
    }

    // Now we need to propagate these through
    // For example, if alias_map is {"w1": ["w2"], "w2": ["w3"]}, it should look like {"w1": ["w2", "w3"], "w2": ["w3"]}
    let mut changed = true;

    while changed {
        changed = false;

        let alias_snapshot = alias_map.clone();

        for (source, dests) in alias_snapshot.iter() {
            let mut new_dests = HashSet::new();

            for dest in dests.iter() {
                if let Some(next_dests) = alias_snapshot.get(&Expr::Net(dest.clone())) {
                    new_dests.extend(next_dests.iter().cloned());
                }
            }

            let entry = alias_map.get_mut(source).unwrap();
            let old_len = entry.len();

            entry.extend(new_dests);

            if entry.len() > old_len {
                changed = true;
            }
        }
    }

    alias_map
}

fn compute_top_mod_outputs(
    netlist: &ModuleNetlist,
    cell_library: &StandardCellLibrary,
    alias_map: &HashMap<Expr, HashSet<String>>,
) -> Vec<String> {
    let mut top_mod_outputs_set: HashSet<String> = netlist.outputs.iter().cloned().collect();

    // We also want all inputs to sequential cells to be considered as outputs of the module
    // This is because an "output" is actually just any information which may be carried forward in time by some memory
    for instance in netlist.instances.values() {
        let cell = cell_library
            .cells
            .get(&instance.cell_type)
            .unwrap_or_else(|| panic!("Unknown standard cell type {}", instance.cell_type));

        if !cell.is_sequential {
            continue;
        }

        for input_pin in &cell.input_pins {
            let Some(Some(connection)) = instance.connections.get(input_pin) else {
                panic!(
                    "Sequential input pin {} on instance {} is not connected",
                    input_pin, instance.name,
                );
            };

            match connection {
                Expr::Net(net_name) => {
                    top_mod_outputs_set.insert(net_name.clone());
                }

                // Constants do not correspond to a wire that needs to be
                // tracked as an effective output.
                Expr::Const(_) => {}

                other => {
                    panic!(
                        "Unsupported expression {:?} connected to sequential input {} on instance {}",
                        other, input_pin, instance.name,
                    );
                }
            }
        }
    }

    for (source, dests) in alias_map {
        let Expr::Net(source_name) = source else {
            continue;
        };

        // If any destination is a top_mod_output (ie is the LHS of assign LHS = source), the source is also effectively an output
        if dests.iter().any(|dest| top_mod_outputs_set.contains(dest)) {
            top_mod_outputs_set.insert(source_name.clone());
        }
    }

    top_mod_outputs_set.into_iter().collect()
}

fn validate_instances(netlist: &ModuleNetlist, cell_library: &StandardCellLibrary) {
    for (_instance_name, inst) in netlist.instances.iter() {
        // Verify that this instance matches with the standard cell library
        if let Some(cell) = cell_library.cells.get(&inst.cell_type) {
            // Check that all input connections exist
            for name in &cell.input_pins {
                inst.connections
                    .get(name)
                    .expect("All inputs must be connected on all standard cell instances")
                    .as_ref()
                    .expect("All inputs must be connected on all standard cell instances");
            }

            for port in inst.connections.keys() {
                assert!(
                    cell.has_pin(port),
                    "Instance port {} does not exist on standard cell {}",
                    port,
                    inst.cell_type,
                );
            }
        } else {
            panic!("Invalid standard cell name: {}", inst.cell_type);
        }
    }
}

fn build_dependency_graph(
    netlist: &ModuleNetlist,
    cell_library: &StandardCellLibrary,
    alias_map: &HashMap<Expr, HashSet<String>>,
) -> DiGraph<String, ()> {
    // create graph
    let mut graph = DiGraph::new();
    let mut nodes = HashMap::new();

    // Iterate through to create nodes
    for (instance_name, _) in netlist.instances.iter() {
        nodes.insert(instance_name.clone(), graph.add_node(instance_name.clone()));
    }

    let mut consumers_by_wire: HashMap<String, Vec<NodeIndex>> = HashMap::new();

    for (consumer_instance_name, consumer_inst) in netlist.instances.iter() {
        let consumer_cell = cell_library.cells.get(&consumer_inst.cell_type).unwrap();
        let consumer_node = *nodes.get(consumer_instance_name).unwrap();

        for input_pin in &consumer_cell.input_pins {
            let Some(Some(input_expr)) = consumer_inst.connections.get(input_pin) else {
                continue;
            };

            match input_expr {
                Expr::Net(net_name) => {
                    consumers_by_wire
                        .entry(net_name.clone())
                        .or_default()
                        .push(consumer_node);
                }
                Expr::Const(_) => {}
                other => {
                    panic!("Unsupported gate input expression: {:?}", other);
                }
            }
        }
    }

    for (instance_name, inst) in netlist.instances.iter() {
        let cell = cell_library
            .cells
            .get(&inst.cell_type)
            .expect("Standard cell does not exist, so check didn't work earlier");

        if cell.is_sequential {
            continue;
        }

        let source_node = *nodes.get(instance_name).unwrap();

        for out_pin in &cell.output_pins {
            if let Some(Some(out_wire_name)) = inst.connections.get(&out_pin.name) {
                let dependent_wires = alias_map.get(out_wire_name).unwrap();

                for dependent_wire in dependent_wires {
                    if let Some(consumers) = consumers_by_wire.get(dependent_wire) {
                        for consumer_node in consumers {
                            graph.update_edge(source_node, *consumer_node, ());
                        }
                    }
                }
            }
        }
    }
    graph
}

fn sorted_gate_order(graph: &DiGraph<String, ()>) -> Vec<NodeIndex> {
    let mut gate_sorted_order = vec![];
    match toposort(&graph, None) {
        Ok(order) => {
            for node_idx in order {
                gate_sorted_order.push(node_idx)
            }
        }
        Err(cycle) => {
            panic!(
                "Graph has a cycle! Cannot sort! Cycle starts at {:?}",
                cycle.node_id()
            );
        }
    }
    gate_sorted_order
}

fn compile_wire_ids(netlist: &ModuleNetlist) -> (HashMap<String, WireId>, Vec<String>) {
    let mut wire_ids = HashMap::new();
    let mut wire_names = Vec::new();

    for wire in netlist.all_declared_nets() {
        if wire_ids.contains_key(wire) {
            // This is okay. A port can also be declared as a wire.
            continue;
        }

        let id = wire_names.len();
        wire_ids.insert(wire.clone(), id);
        wire_names.push(wire.clone());
    }

    (wire_ids, wire_names)
}

fn compile_alias_wire_ids(
    alias_map: &HashMap<Expr, HashSet<String>>,
    wire_ids: &HashMap<String, usize>,
    num_wires: usize,
) -> Vec<Vec<usize>> {
    let mut alias_wire_ids = vec![Vec::new(); num_wires];

    for (source, dests) in alias_map.iter() {
        let Expr::Net(source_name) = source else {
            continue;
        };

        let source_id = *wire_ids
            .get(source_name)
            .unwrap_or_else(|| panic!("Unknown source wire in alias map: {}", source_name));

        for dest in dests {
            let dest_id = *wire_ids
                .get(dest)
                .unwrap_or_else(|| panic!("Unknown dest wire in alias map: {}", dest));

            alias_wire_ids[source_id].push(dest_id);
        }
    }
    alias_wire_ids
}

fn compile_sequential_io(
    netlist: &ModuleNetlist,
    cell_library: &StandardCellLibrary,
    wire_ids: &HashMap<String, WireId>,
) -> (Vec<WireId>, Vec<WireId>) {
    let mut sequential_output_wires = Vec::new();
    let mut sequential_input_wires = Vec::new();

    for instance in netlist.instances.values() {
        let cell = cell_library.cells.get(&instance.cell_type).unwrap();

        if !cell.is_sequential {
            continue;
        }

        for name in &cell.sequential_output_pins {
            if let Some(Some(Expr::Net(out_net))) = instance.connections.get(name) {
                let wire_id = *wire_ids
                    .get(out_net)
                    .unwrap_or_else(|| panic!("Unknown sequential output net {}", out_net));

                sequential_output_wires.push(wire_id);
            }
        }

        for out_pin in &cell.output_pins {
            if let Some(Some(Expr::Net(out_net))) = instance.connections.get(&out_pin.name) {
                let wire_id = *wire_ids
                    .get(out_net)
                    .unwrap_or_else(|| panic!("Unknown sequential output net {}", out_net));

                sequential_output_wires.push(wire_id);
            }
        }

        for name in &cell.input_pins {
            let expr = instance.connections.get(name).unwrap().clone().unwrap();

            match expr {
                Expr::Net(net_name) => {
                    let wire_id = *wire_ids
                        .get(&net_name)
                        .unwrap_or_else(|| panic!("Unknown sequential input net {}", net_name));

                    sequential_input_wires.push(wire_id);
                }
                Expr::Const(_) => {
                    // Constants connected to sequential inputs are not wires.
                }
                other => {
                    panic!("Unsupported sequential input expression: {:?}", other);
                }
            }
        }
    }

    (sequential_output_wires, sequential_input_wires)
}

fn compile_constant_writes(
    alias_map: &HashMap<Expr, HashSet<String>>,
    wire_ids: &HashMap<String, WireId>,
) -> Vec<(WireId, Bit)> {
    let mut constant_writes = Vec::new();

    for (source, dests) in alias_map {
        let Expr::Const(c) = source else {
            continue;
        };

        let value =
            parse_one_bit_const(c).unwrap_or_else(|| panic!("Unsupported assigned constant {}", c));

        for dest in dests {
            let wire_id = *wire_ids
                .get(dest)
                .unwrap_or_else(|| panic!("Unknown const-assigned wire {}", dest));

            constant_writes.push((wire_id, value));
        }
    }

    constant_writes
}

fn compile_gates(
    netlist: &ModuleNetlist,
    cell_library: &StandardCellLibrary,
    graph: &DiGraph<String, ()>,
    gate_sorted_order: &Vec<NodeIndex>,
    wire_ids: &HashMap<String, usize>,
    alias_wire_ids: &Vec<Vec<usize>>,
) -> Vec<CompiledGate> {
    let mut compiled_gates = Vec::new();

    for node_idx in gate_sorted_order {
        let inst_name = &graph[*node_idx];
        let inst = netlist.instances.get(inst_name).unwrap();
        let cell = cell_library.cells.get(&inst.cell_type).unwrap();

        if cell.is_sequential {
            continue;
        }

        let mut inputs = Vec::with_capacity(cell.input_pins.len());

        for input_pin in &cell.input_pins {
            let expr = inst.connections.get(input_pin).unwrap().clone().unwrap();

            let sim_input = match expr {
                Expr::Net(net_name) => {
                    let id = *wire_ids
                        .get(&net_name)
                        .unwrap_or_else(|| panic!("Unknown input net {}", net_name));

                    SimInput::Wire(id)
                }
                Expr::Const(c) => {
                    let bit = parse_one_bit_const(&c)
                        .unwrap_or_else(|| panic!("Unsupported constant {}", c));

                    SimInput::Const(bit)
                }
                other => {
                    panic!("Unsupported gate input expression {:?}", other);
                }
            };

            inputs.push(sim_input);
        }

        let mut outputs = Vec::new();

        for out_pin in &cell.output_pins {
            if let Some(Some(Expr::Net(out_net))) = inst.connections.get(&out_pin.name) {
                let out_id = *wire_ids
                    .get(out_net)
                    .unwrap_or_else(|| panic!("Unknown output net {}", out_net));

                outputs.push(CompiledOutput {
                    wire_name: out_net.clone(),
                    function: out_pin.function.clone(),
                    alias_wires: alias_wire_ids[out_id].clone(),
                });
            }
        }

        let output_alias_wires = outputs
            .iter()
            .flat_map(|output| output.alias_wires.iter().copied())
            .collect();

        compiled_gates.push(CompiledGate {
            instance_name: inst_name.clone(),
            inputs,
            outputs,
            output_alias_wires,
        });
    }
    compiled_gates
}

fn parse_one_bit_const(s: &str) -> Option<Bit> {
    let s = s.replace('_', "").to_ascii_lowercase();

    match s.as_str() {
        "0" | "1'b0" | "1'h0" | "1'd0" => Some(Bit::Low),
        "1" | "1'b1" | "1'h1" | "1'd1" => Some(Bit::High),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use core::panic;
    use std::{
        path::PathBuf,
        sync::atomic::{AtomicUsize, Ordering},
    };

    use super::*;

    static TEST_FILE_COUNTER: AtomicUsize = AtomicUsize::new(0);

    fn write_temp_file(prefix: &str, contents: &str) -> String {
        let id = TEST_FILE_COUNTER.fetch_add(1, Ordering::Relaxed);
        let mut path: PathBuf = std::env::temp_dir();
        path.push(format!(
            "isa_minimization_{}_{}_{}.v",
            prefix,
            std::process::id(),
            id
        ));
        fs::write(&path, contents).unwrap();
        path.to_string_lossy().into_owned()
    }

    fn optimize_test_netlist(
        verilog: &str,
        bit_inputs: Vec<HashMap<String, Bit>>,
    ) -> GateUsageOptimization {
        let netlist_path = write_temp_file("netlist", verilog);
        let simulator =
            Simulator::from_file(&netlist_path, "examples/NangateOpenCellLibrary_typical.lib");
        simulator.optimize_gate_usage_details(&bit_inputs)
    }

    fn optimize_and_validate_test_netlist(
        verilog: &str,
        bit_inputs: Vec<HashMap<String, Bit>>,
    ) -> (GateUsageOptimization, OptimizationValidation) {
        let netlist_path = write_temp_file("netlist", verilog);
        let simulator =
            Simulator::from_file(&netlist_path, "examples/NangateOpenCellLibrary_typical.lib");
        let compiled_inputs = simulator.compile_optimization_inputs(&bit_inputs);
        let mut workspace = simulator.optimization_workspace();
        let optimization = simulator
            .optimize_compiled_gate_usage_details_with_workspace(&compiled_inputs, &mut workspace);
        let validation = simulator.validate_compiled_gate_usage_optimization_with_workspace(
            &compiled_inputs,
            &optimization,
            &mut workspace,
        );

        (optimization, validation)
    }

    fn optimize_with_fresh_workspace(
        simulator: &Simulator,
        bit_inputs: &Vec<HashMap<String, Bit>>,
    ) -> GateUsageOptimization {
        let compiled_inputs = simulator.compile_optimization_inputs(bit_inputs);
        let mut workspace = simulator.optimization_workspace();
        simulator
            .optimize_compiled_gate_usage_details_with_workspace(&compiled_inputs, &mut workspace)
    }

    fn simulate_test_netlist(
        verilog: &str,
        bit_input: HashMap<String, Bit>,
    ) -> HashMap<String, Bit> {
        let netlist_path = write_temp_file("netlist", verilog);
        let simulator =
            Simulator::from_file(&netlist_path, "examples/NangateOpenCellLibrary_typical.lib");
        simulator.simulate(&bit_input, &mut HashSet::new())
    }

    fn test_input(values: &[(&str, Bit)]) -> HashMap<String, Bit> {
        values
            .iter()
            .map(|(name, value)| ((*name).to_string(), *value))
            .collect()
    }

    #[test]
    fn exposes_primary_input_wire_names() {
        let verilog = r#"
            module top(input [3:0] a, input b, output y);
                assign y = a[0];
            endmodule
        "#;
        let netlist_path = write_temp_file("netlist", verilog);
        let simulator =
            Simulator::from_file(&netlist_path, "examples/NangateOpenCellLibrary_typical.lib");

        assert_eq!(
            simulator.input_wire_names(),
            &[
                "a[0]".to_string(),
                "a[1]".to_string(),
                "a[2]".to_string(),
                "a[3]".to_string(),
                "b".to_string()
            ]
        );
    }

    #[test]
    fn converts_instruction_pattern_to_primary_sim_inputs() {
        let verilog = r#"
            module top(input [3:0] instruction_word, input ready, output y);
                assign y = instruction_word[0];
            endmodule
        "#;
        let netlist_path = write_temp_file("netlist", verilog);
        let simulator =
            Simulator::from_file(&netlist_path, "examples/NangateOpenCellLibrary_typical.lib");

        let sim_inputs =
            simulator.pattern_to_sim_inputs(&BitPattern::parse("1010"), "instruction_word");

        assert_eq!(sim_inputs["instruction_word[0]"], Bit::Low);
        assert_eq!(sim_inputs["instruction_word[1]"], Bit::High);
        assert_eq!(sim_inputs["instruction_word[2]"], Bit::Low);
        assert_eq!(sim_inputs["instruction_word[3]"], Bit::High);
        assert_eq!(sim_inputs["ready"], Bit::Var);
    }

    #[test]
    fn optimize_retains_output_that_is_only_observably_static() {
        let verilog = r#"
module obs_static(a, b, sel, out);
  input a, b, sel;
  output out;
  wire a, b, sel, out, n0;
  AND2_X1 g_and(.A1 (a), .A2 (sel), .ZN (n0));
  MUX2_X1 g_mux(.A (n0), .B (b), .S (sel), .Z (out));
endmodule
"#;
        let bit_inputs = vec![
            test_input(&[("a", Bit::Low), ("b", Bit::Var), ("sel", Bit::Low)]),
            test_input(&[("a", Bit::High), ("b", Bit::Var), ("sel", Bit::Low)]),
            test_input(&[("a", Bit::Low), ("b", Bit::Var), ("sel", Bit::High)]),
            test_input(&[("a", Bit::High), ("b", Bit::Var), ("sel", Bit::High)]),
        ];

        let optimization = optimize_test_netlist(verilog, bit_inputs);

        assert!(!optimization.gates_to_comment.contains(&"g_and".to_string()));
        assert!(
            !optimization
                .assignments
                .iter()
                .any(|assignment| { assignment.wire_name == "n0" })
        );
    }

    #[test]
    fn optimize_retains_never_needed_nonconstant_output() {
        let verilog = r#"
module never_needed(a, out);
  input a;
  output out;
  wire a, out, unused;
  BUF_X1 g_unused(.A (a), .Z (unused));
  BUF_X1 g_out(.A (a), .Z (out));
endmodule
"#;
        let bit_inputs = vec![test_input(&[("a", Bit::Var)])];

        let optimization = optimize_test_netlist(verilog, bit_inputs);

        assert!(
            !optimization
                .gates_to_comment
                .contains(&"g_unused".to_string())
        );
        assert!(
            !optimization
                .assignments
                .iter()
                .any(|assignment| { assignment.wire_name == "unused" })
        );
    }

    #[test]
    fn optimize_rejects_incompatible_arbitrary_substitutions() {
        let verilog = r#"
module incompatible_arbitrary(d, out);
  input d;
  output out;
  wire d, out, a, b, either;
  BUF_X1 g_a(.A (1'b1), .Z (a));
  BUF_X1 g_b(.A (1'b1), .Z (b));
  OR2_X1 g_or(.A1 (a), .A2 (b), .ZN (either));
  XOR2_X1 g_out(.A (either), .B (d), .Z (out));
endmodule
"#;
        let unsafely_optimized_verilog = r#"
module incompatible_arbitrary(d, out);
  input d;
  output out;
  wire d, out, a, b, either;
  assign a = 1'b0;
  assign b = 1'b0;
  OR2_X1 g_or(.A1 (a), .A2 (b), .ZN (either));
  XOR2_X1 g_out(.A (either), .B (d), .Z (out));
endmodule
"#;
        let optimization = optimize_test_netlist(verilog, vec![test_input(&[("d", Bit::Var)])]);

        let original_outputs = simulate_test_netlist(verilog, test_input(&[("d", Bit::Low)]));
        let optimized_outputs =
            simulate_test_netlist(unsafely_optimized_verilog, test_input(&[("d", Bit::Low)]));
        assert_eq!(original_outputs["out"], Bit::High);
        assert_eq!(optimized_outputs["out"], Bit::Low);

        assert!(optimization.gates_to_comment.contains(&"g_a".to_string()));
        assert!(optimization.gates_to_comment.contains(&"g_b".to_string()));
        assert!(optimization.assignments.contains(&GateOutputAssignment {
            wire_name: "a".to_string(),
            value: Bit::High,
        }));
        assert!(optimization.assignments.contains(&GateOutputAssignment {
            wire_name: "b".to_string(),
            value: Bit::High,
        }));
    }

    #[test]
    fn optimize_rejects_observably_static_substitutions_that_change_observability() {
        let verilog = r#"
module incompatible_observable_static(p, out);
  input p;
  output out;
  wire p, out, data, select;
  INV_X1 g_data(.A (p), .ZN (data));
  INV_X1 g_select(.A (p), .ZN (select));
  MUX2_X1 g_out(.A (data), .B (1'b1), .S (select), .Z (out));
endmodule
"#;
        let unsafely_optimized_verilog = r#"
module incompatible_observable_static(p, out);
  input p;
  output out;
  wire p, out, data, select;
  assign data = 1'b0;
  assign select = 1'b0;
  MUX2_X1 g_out(.A (data), .B (1'b1), .S (select), .Z (out));
endmodule
"#;
        let bit_inputs = vec![
            test_input(&[("p", Bit::Low)]),
            test_input(&[("p", Bit::High)]),
        ];
        let optimization = optimize_test_netlist(verilog, bit_inputs);

        let original_outputs = simulate_test_netlist(verilog, test_input(&[("p", Bit::Low)]));
        let optimized_outputs =
            simulate_test_netlist(unsafely_optimized_verilog, test_input(&[("p", Bit::Low)]));
        assert_eq!(original_outputs["out"], Bit::High);
        assert_eq!(optimized_outputs["out"], Bit::Low);

        assert!(
            !optimization
                .gates_to_comment
                .contains(&"g_data".to_string())
        );
        assert!(
            !optimization
                .gates_to_comment
                .contains(&"g_select".to_string())
        );
    }

    #[test]
    fn optimize_does_not_assign_needed_variable_output() {
        let verilog = r#"
module needed_var(a, out);
  input a;
  output out;
  wire a, out;
  BUF_X1 g_buf(.A (a), .Z (out));
endmodule
"#;
        let bit_inputs = vec![test_input(&[("a", Bit::Var)])];

        let optimization = optimize_test_netlist(verilog, bit_inputs);

        assert_eq!(optimization.gates_to_comment, Vec::<String>::new());
        assert_eq!(optimization.assignments, Vec::<GateOutputAssignment>::new());
    }

    #[test]
    fn optimize_replaces_and_validates_globally_static_gate() {
        let verilog = r#"
module globally_static(a, b, out);
  input a, b;
  output out;
  wire a, b, out, forced;
  OR2_X1 g_static(.A1 (a), .A2 (1'b1), .ZN (forced));
  XOR2_X1 g_out(.A (forced), .B (b), .Z (out));
endmodule
"#;
        let (optimization, validation) = optimize_and_validate_test_netlist(
            verilog,
            vec![test_input(&[("a", Bit::Var), ("b", Bit::Var)])],
        );

        assert!(
            optimization
                .gates_to_comment
                .contains(&"g_static".to_string())
        );
        assert!(optimization.assignments.contains(&GateOutputAssignment {
            wire_name: "forced".to_string(),
            value: Bit::High,
        }));
        assert_eq!(validation.input_patterns_checked, 1);
        assert!(validation.effective_outputs_checked >= 1);
        assert_eq!(validation.replacement_outputs_checked, 1);
    }

    #[test]
    fn public_optimization_wrappers_and_exported_wires_use_compiled_simulator() {
        let verilog = r#"
module wrapper_paths(a, b, out);
  input a, b;
  output out;
  wire a, b, out, forced;
  OR2_X1 g_static(.A1 (a), .A2 (1'b1), .ZN (forced));
  XOR2_X1 g_out(.A (forced), .B (b), .Z (out));
endmodule
"#;
        let netlist_path = write_temp_file("netlist", verilog);
        let simulator =
            Simulator::from_file(&netlist_path, "examples/NangateOpenCellLibrary_typical.lib");
        let bit_inputs = vec![test_input(&[("a", Bit::Var), ("b", Bit::Var)])];

        assert_eq!(
            simulator.optimize_gate_usage(&bit_inputs),
            vec!["g_out".to_string()]
        );

        let batch = simulator.optimize_gate_usage_details_batch(&[bit_inputs.clone()]);
        assert_eq!(batch.len(), 1);
        assert!(batch[0].gates_to_comment.contains(&"g_static".to_string()));

        let validation = simulator.validate_gate_usage_optimization(&bit_inputs, &batch[0]);
        assert_eq!(validation.input_patterns_checked, 1);
        assert_eq!(validation.replacement_outputs_checked, 1);

        let a_wire = simulator.wire_ids["a"];
        assert_eq!(
            simulator.export_nonarbitrary_wires(&HashSet::from([a_wire])),
            HashSet::from([Expr::Net("a".to_string())])
        );
    }

    #[test]
    fn count_only_optimization_matches_detailed_removed_gate_count() {
        let verilog = r#"
module count_only(a, b, out);
  input a, b;
  output out;
  wire a, b, out, forced;
  OR2_X1 g_static(.A1 (a), .A2 (1'b1), .ZN (forced));
  XOR2_X1 g_out(.A (forced), .B (b), .Z (out));
endmodule
"#;
        let netlist_path = write_temp_file("netlist", verilog);
        let simulator =
            Simulator::from_file(&netlist_path, "examples/NangateOpenCellLibrary_typical.lib");
        let bit_inputs = vec![test_input(&[("a", Bit::Var), ("b", Bit::Var)])];
        let compiled_inputs = simulator.compile_optimization_inputs(&bit_inputs);

        let mut detail_workspace = simulator.optimization_workspace();
        let details = simulator.optimize_compiled_gate_usage_details_with_workspace(
            &compiled_inputs,
            &mut detail_workspace,
        );
        let mut count_workspace = simulator.optimization_workspace();
        let count = simulator.optimize_compiled_gate_usage_count_with_workspace(
            &compiled_inputs,
            &mut count_workspace,
        );

        assert_eq!(count, details.gates_to_comment.len());
    }

    #[test]
    fn reused_optimization_workspace_matches_fresh_workspaces_for_consecutive_runs() {
        let verilog = r#"
module workspace_reuse(a, b, out);
  input a, b;
  output out;
  wire a, b, out, n;
  BUF_X1 g_buf(.A (a), .Z (n));
  XOR2_X1 g_out(.A (n), .B (b), .Z (out));
endmodule
"#;
        let netlist_path = write_temp_file("netlist", verilog);
        let simulator =
            Simulator::from_file(&netlist_path, "examples/NangateOpenCellLibrary_typical.lib");
        let constant_inputs = vec![test_input(&[("a", Bit::Low), ("b", Bit::Var)])];
        let variable_inputs = vec![test_input(&[("a", Bit::Var), ("b", Bit::Var)])];

        let fresh_results = vec![
            optimize_with_fresh_workspace(&simulator, &constant_inputs),
            optimize_with_fresh_workspace(&simulator, &variable_inputs),
            optimize_with_fresh_workspace(&simulator, &constant_inputs),
        ];

        let consecutive_inputs = vec![
            constant_inputs.clone(),
            variable_inputs.clone(),
            constant_inputs.clone(),
        ];
        let mut reused_workspace = simulator.optimization_workspace();
        let reused_results = consecutive_inputs
            .iter()
            .map(|inputs| {
                let compiled_inputs = simulator.compile_optimization_inputs(inputs);
                simulator.optimize_compiled_gate_usage_details_with_workspace(
                    &compiled_inputs,
                    &mut reused_workspace,
                )
            })
            .collect::<Vec<_>>();

        assert_eq!(reused_results, fresh_results);
        assert!(
            reused_results[0]
                .gates_to_comment
                .contains(&"g_buf".to_string()),
            "constant-input run should remove g_buf"
        );
        assert!(
            !reused_results[1]
                .gates_to_comment
                .contains(&"g_buf".to_string()),
            "variable-input run should not inherit g_buf removal from the previous run"
        );
    }

    #[test]
    fn validation_checks_top_level_outputs_and_sequential_inputs() {
        let verilog = r#"
module effective_outputs(a, clk, out);
  input a, clk;
  output out;
  wire a, clk, out, d, q;
  OR2_X1 g_static(.A1 (a), .A2 (1'b1), .ZN (d));
  DFF_X1 state(.D (d), .CK (clk), .Q (q));
  BUF_X1 g_out(.A (q), .Z (out));
endmodule
"#;
        let (optimization, validation) = optimize_and_validate_test_netlist(
            verilog,
            vec![test_input(&[("a", Bit::Var), ("clk", Bit::Var)])],
        );

        assert!(
            optimization
                .gates_to_comment
                .contains(&"g_static".to_string())
        );
        assert_eq!(
            validation.effective_outputs_checked, 3,
            "the top-level output and both DFF inputs must be compared"
        );
    }

    #[test]
    #[should_panic(expected = "post-optimization validation rejected")]
    fn validation_rejects_nonconstant_replacement() {
        let verilog = r#"
module invalid_replacement(a, out);
  input a;
  output out;
  wire a, out;
  BUF_X1 g_out(.A (a), .Z (out));
endmodule
"#;
        let netlist_path = write_temp_file("netlist", verilog);
        let simulator =
            Simulator::from_file(&netlist_path, "examples/NangateOpenCellLibrary_typical.lib");
        let inputs = simulator.compile_optimization_inputs(&vec![test_input(&[("a", Bit::Var)])]);
        let mut workspace = simulator.optimization_workspace();
        let invalid_optimization = GateUsageOptimization {
            gates_to_comment: vec!["g_out".to_string()],
            assignments: vec![GateOutputAssignment {
                wire_name: "out".to_string(),
                value: Bit::Low,
            }],
        };

        simulator.validate_compiled_gate_usage_optimization_with_workspace(
            &inputs,
            &invalid_optimization,
            &mut workspace,
        );
    }

    #[test]
    fn optimize_retains_multi_output_gate_that_is_not_globally_static() {
        let liberty = r#"
library(test) {
  cell (DUAL_X1) {
    pin (A) { direction : input; }
    pin (B) { direction : input; }
    pin (S) { direction : input; }
    pin (Z0) { direction : output; function : "(A & S)"; }
    pin (Z1) { direction : output; function : "B"; }
  }
  cell (MUX2_X1) {
    pin (A) { direction : input; }
    pin (B) { direction : input; }
    pin (S) { direction : input; }
    pin (Z) { direction : output; function : "((S & B) | (A & !S))"; }
  }
}
"#;
        let verilog = r#"
module mixed_output(a, b, sel, out);
  input a, b, sel;
  output out;
  wire a, b, sel, out, n0, n1;
  DUAL_X1 g_dual(.A (a), .B (b), .S (sel), .Z0 (n0), .Z1 (n1));
  MUX2_X1 g_mux(.A (n0), .B (b), .S (sel), .Z (out));
endmodule
"#;
        let liberty_path = write_temp_file("lib", liberty);
        let netlist_path = write_temp_file("netlist", verilog);
        let simulator = Simulator::from_file(&netlist_path, &liberty_path);
        let bit_inputs = vec![
            test_input(&[("a", Bit::Low), ("b", Bit::Var), ("sel", Bit::Low)]),
            test_input(&[("a", Bit::High), ("b", Bit::Var), ("sel", Bit::Low)]),
            test_input(&[("a", Bit::Low), ("b", Bit::Var), ("sel", Bit::High)]),
            test_input(&[("a", Bit::High), ("b", Bit::Var), ("sel", Bit::High)]),
        ];

        let optimization = simulator.optimize_gate_usage_details(&bit_inputs);

        assert!(
            !optimization
                .gates_to_comment
                .contains(&"g_dual".to_string())
        );
        assert!(
            !optimization
                .assignments
                .iter()
                .any(|assignment| { assignment.wire_name == "n0" || assignment.wire_name == "n1" })
        );
    }

    #[test]
    fn alu_sim_test() {
        let simulator = Simulator::from_file(
            "examples/alu_syn.v",
            "examples/NangateOpenCellLibrary_typical.lib",
        );
        let mut wires_nonarbitrary = HashSet::new();
        // Checks addition on an example ALU
        let mut bit_input = HashMap::from([
            ("b[7]".into(), Bit::High),
            ("b[6]".into(), Bit::Low),
            ("b[5]".into(), Bit::Low),
            ("b[4]".into(), Bit::Low),
            ("b[3]".into(), Bit::Low),
            ("b[2]".into(), Bit::Low),
            ("b[1]".into(), Bit::Low),
            ("b[0]".into(), Bit::High),
            ("a_sel".into(), Bit::Low),
            ("sel".into(), Bit::Low),
            ("ctrl[2]".into(), Bit::Low),
            ("ctrl[1]".into(), Bit::Low),
            ("ctrl[0]".into(), Bit::Low),
        ]);
        for a in 0u8..=255 {
            for bit_idx in 0..8 {
                let bit_val = (a >> bit_idx) & 1;
                let bit = match bit_val {
                    0 => Bit::Low,
                    1 => Bit::High,
                    _ => panic!("How?"),
                };
                bit_input.insert(format!("a0_mux[{}]", bit_idx), bit);
                bit_input.insert(format!("a1_mux[{}]", bit_idx), bit);
            }
            println!("{}", a);
            for b in 0u8..=255 {
                for bit_idx in 0..8 {
                    let bit_val = (b >> bit_idx) & 1;
                    let bit = match bit_val {
                        0 => Bit::Low,
                        1 => Bit::High,
                        _ => panic!("How?"),
                    };
                    bit_input.insert(format!("b[{}]", bit_idx), bit);
                }
                let wires = simulator.simulate(&bit_input, &mut wires_nonarbitrary);
                let output_val: u8 = (0..=7)
                    .map(|i| match wires.get(&format!("out[{i}]")).unwrap() {
                        Bit::High => 1 << i,
                        Bit::Low => 0,
                        _ => panic!("Output should not have any variable or test bits!"),
                    })
                    .sum();
                assert_eq!(output_val, a.overflowing_add(b).0, "Result should match!");
            }
        }
        // let (wires, wires_nonarbitrary) = simulator.simulate(&bit_input, wires_nonarbitrary);
        // println!("");
        // panic!();
    }
}
