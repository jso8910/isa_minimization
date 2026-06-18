use std::{
    collections::{HashMap, HashSet},
    fs,
};

use petgraph::{
    algo::toposort,
    graph::{DiGraph, NodeIndex},
};

use crate::{
    bit::Bit,
    parser::{parse_netlist, Expr, ModuleNetlist},
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
pub struct Simulator {
    top_mod_output_wire_ids: Vec<WireId>,

    // Compiled simulation fields using node indices
    // compiled_gates is sorted by the topological sort order of the digraph
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
    pub used_gates: Vec<String>,
    pub gates_to_comment: Vec<String>,
    pub assignments: Vec<GateOutputAssignment>,
    pub static_gates: Vec<String>,
    pub observably_static_gates: Vec<String>,
    pub arbitrary_gates: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct CompiledOptimizationInputs {
    // Each optimization input pattern after translating net names to dense wire ids. This avoids
    // doing string/hash lookups every time we simulate the same pattern set.
    inputs: Vec<Vec<(WireId, Bit)>>,
}

#[derive(Debug)]
pub struct OptimizationWorkspace {
    // Reused full-circuit wire values for one simulated input pattern. This is cleared between
    // patterns, but the allocation is kept.
    wires: Vec<Option<Bit>>,

    // Marks wires that are currently needed by the reverse sensitivity walk. Instead of clearing a
    // Vec<bool> for every input pattern, each marked wire stores `current_generation`. A wire is
    // currently needed iff needed_generation[wire_id] == current_generation.
    needed_generation: Vec<u32>,

    // Monotonic marker id for `needed_generation`. Incrementing this logically clears the whole
    // needed set in O(1). If it wraps, we physically clear the vector and restart at 1.
    current_generation: u32,

    // Reused scratch vector holding the input values for the gate currently being sensitivity
    // checked.
    input_values: Vec<Bit>,

    // Accumulated across all input patterns. gates_impact_output[i] is true if gate i affects an
    // effective output for at least one input pattern.
    gates_impact_output: Vec<bool>,

    // For each gate output, the concrete value seen so far if that output is still possibly
    // static. `None` means either no pattern has been processed yet for that output, or the shape
    // has just been reset.
    static_output_values: Vec<Vec<Option<Bit>>>,

    // For each gate output, true until we observe either Bit::Var/Bit::Test or a concrete value
    // different from `static_output_values`.
    output_is_static: Vec<Vec<bool>>,

    // For each gate output, whether that output was needed by the reverse sensitivity walk for at
    // least one input pattern. Outputs that are never needed can be assigned arbitrary constants.
    output_was_needed: Vec<Vec<bool>>,

    // Like `static_output_values`, but only across patterns where the output was observable. This
    // lets us replace gates whose output may vary globally but is constant whenever downstream
    // logic can actually see it.
    needed_static_output_values: Vec<Vec<Option<Bit>>>,

    // Like `output_is_static`, but only invalidated by patterns where the output was observable.
    needed_output_is_static: Vec<Vec<bool>>,
}

impl OptimizationWorkspace {
    fn new(wire_count: usize, gates: &[CompiledGate]) -> Self {
        Self {
            wires: vec![None; wire_count],
            needed_generation: vec![0; wire_count],
            current_generation: 0,
            input_values: Vec::new(),
            gates_impact_output: vec![false; gates.len()],
            static_output_values: gates
                .iter()
                .map(|gate| vec![None; gate.outputs.len()])
                .collect(),
            output_is_static: gates
                .iter()
                .map(|gate| vec![true; gate.outputs.len()])
                .collect(),
            output_was_needed: gates
                .iter()
                .map(|gate| vec![false; gate.outputs.len()])
                .collect(),
            needed_static_output_values: gates
                .iter()
                .map(|gate| vec![None; gate.outputs.len()])
                .collect(),
            needed_output_is_static: gates
                .iter()
                .map(|gate| vec![true; gate.outputs.len()])
                .collect(),
        }
    }

    fn reset_for(&mut self, wire_count: usize, gates: &[CompiledGate]) {
        // Called once at the start of a complete optimization run. It clears all results that must
        // be accumulated over the whole input-pattern set while retaining allocations.
        self.reset_wires(wire_count);

        self.needed_generation.resize(wire_count, 0);

        self.gates_impact_output.clear();
        self.gates_impact_output.resize(gates.len(), false);

        resize_gate_output_bits(&mut self.static_output_values, gates, None);
        resize_gate_output_bits(&mut self.output_is_static, gates, true);
        resize_gate_output_bits(&mut self.output_was_needed, gates, false);
        resize_gate_output_bits(&mut self.needed_static_output_values, gates, None);
        resize_gate_output_bits(&mut self.needed_output_is_static, gates, true);
    }

    fn reset_wires(&mut self, wire_count: usize) {
        // Called for each input pattern. Wire values are pattern-specific, so these cannot be
        // preserved across simulations.
        self.wires.clear();
        self.wires.resize(wire_count, None);
    }

    fn next_needed_generation(&mut self) {
        // Called for each input pattern before the reverse walk. Advancing the generation makes all
        // previous needed-wire markings invisible without clearing the vector.
        self.current_generation = self.current_generation.wrapping_add(1);

        if self.current_generation == 0 {
            self.needed_generation.fill(0);
            self.current_generation = 1;
        }
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
            wire_ids,
            wire_names,
            alias_wire_ids,
            compiled_gates,

            sequential_output_wires,
            sequential_input_wires,
            constant_writes,
        }
    }

    pub fn optimization_workspace(&self) -> OptimizationWorkspace {
        OptimizationWorkspace::new(self.wire_names.len(), &self.compiled_gates)
    }

    /// Computes, for a given set of valid inputs to the module, which gates are necessary to
    /// produce all effective outputs. Effective outputs include both module-level outputs and
    /// inputs to sequential gates, since sequential inputs carry information into future cycles.
    ///
    /// This uses a reverse sensitivity pass. For each input pattern, we first simulate the whole
    /// circuit once. Then we walk gates backward from the effective outputs, marking each gate that
    /// drives a needed wire and recursively marking only the input wires that can affect those
    /// needed outputs.
    /// # Arguments
    /// * `bit_inputs` - A list of inputs to the module to test
    ///
    /// # Returns
    /// * `Vec<String>` - A list of all the instance names in the module which aren't redundant for this set of inputs (ie which affect the output)
    pub fn optimize_gate_usage(&self, bit_inputs: &Vec<HashMap<String, Bit>>) -> Vec<String> {
        self.optimize_gate_usage_details(bit_inputs).used_gates
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
        // Clear all state that is accumulated over an entire optimization run: used gates,
        // static-output tracking, and the current pattern's wire values. The vectors keep their
        // allocations so repeated runs stay cheap.
        workspace.reset_for(self.wire_names.len(), &self.compiled_gates);

        for bit_input in &bit_inputs.inputs {
            // Each input pattern needs a fresh simulated wire state. Other workspace fields, such
            // as gates_impact_output and static-output tracking, intentionally persist across all
            // patterns in this optimization run.
            workspace.reset_wires(self.wire_names.len());
            self.apply_primary_wire_inputs(bit_input, &mut workspace.wires);
            self.apply_sequential_outputs(&mut workspace.wires);
            self.apply_constant_assigns(&mut workspace.wires);
            self.simulate_compiled_gates_range(&mut workspace.wires, 0, self.compiled_gates.len());

            // DEBUG: every wire produced by a compiled gate, plus every effective output, should
            // have a value after a full simulation. If this fails, the netlist was not fully
            // simulated for this input pattern.
            assert!(self
                .compiled_gates
                .iter()
                .flat_map(|gate| gate.output_alias_wires.iter())
                .chain(self.top_mod_output_wire_ids.iter())
                .all(|wire_id| workspace.wires[*wire_id].is_some()));

            // Track outputs that are constant over every supplied input pattern. Only concrete
            // low/high values count as static; Bit::Var means the value still depends on an
            // unconstrained input, so assigning a constant would be unsound.
            for (gate_idx, gate) in self.compiled_gates.iter().enumerate() {
                for (output_idx, output) in gate.outputs.iter().enumerate() {
                    if !workspace.output_is_static[gate_idx][output_idx] {
                        continue;
                    }

                    let wire_id = output.alias_wires[0];
                    let value = workspace.wires[wire_id].unwrap();

                    if !matches!(value, Bit::Low | Bit::High) {
                        workspace.output_is_static[gate_idx][output_idx] = false;
                        continue;
                    }

                    match workspace.static_output_values[gate_idx][output_idx] {
                        Some(prev) if prev != value => {
                            workspace.output_is_static[gate_idx][output_idx] = false;
                        }
                        Some(_) => {}
                        None => workspace.static_output_values[gate_idx][output_idx] = Some(value),
                    }
                }
            }

            // Start from the effective outputs. As we walk backward, this set grows to include
            // upstream wires whose values can influence those outputs for this input pattern.
            //
            // `needed_generation` is the per-pattern needed set. Advancing the generation is the
            // equivalent of clearing that set, but avoids touching every wire for every pattern.
            workspace.next_needed_generation();
            for &wire_id in &self.top_mod_output_wire_ids {
                self.mark_wire_and_aliases_needed(wire_id, workspace);
            }

            // Traverse netlist in reverse topological order
            for gate_idx in (0..self.compiled_gates.len()).rev() {
                let gate = &self.compiled_gates[gate_idx];

                // If none of this gate's outputs feed a currently-needed wire, this gate cannot
                // affect any effective output discovered so far.
                // Since we are going in reverse order, all outputs which come downstream of this gate
                // should have already been discovered
                let gate_output_needed = gate
                    .output_alias_wires
                    .iter()
                    .any(|&wire_id| self.wire_is_needed(wire_id, workspace));

                if !gate_output_needed {
                    continue;
                }

                workspace.gates_impact_output[gate_idx] = true;

                // Reconstruct this gate's simulated input vector from the full-circuit simulation.
                // We use these concrete/symbolic values for local sensitivity checks below.
                // The vector allocation is reused for every gate.
                workspace.input_values.clear();
                for input in &gate.inputs {
                    let value = read_sim_input(&workspace.wires, input)
                        .unwrap_or_else(|| panic!("No simulated value for input {:?}", input));

                    workspace.input_values.push(value);
                }

                for input_idx in 0..gate.inputs.len() {
                    let SimInput::Wire(wire_id) = gate.inputs[input_idx] else {
                        continue;
                    };

                    if self.wire_or_alias_is_needed(wire_id, workspace) {
                        continue;
                    }

                    // Locally perturb one gate input to Bit::Test. If any needed output of this
                    // gate becomes Bit::Test, that input wire is necessary and must be followed
                    // farther backward.
                    let old_value =
                        std::mem::replace(&mut workspace.input_values[input_idx], Bit::Test);

                    let is_sensitive = gate.outputs.iter().any(|output| {
                        output
                            .alias_wires
                            .iter()
                            .any(|&wire_id| self.wire_is_needed(wire_id, workspace))
                            && output.function.evaluate(&workspace.input_values) == Bit::Test
                    });

                    workspace.input_values[input_idx] = old_value;

                    if is_sensitive {
                        self.mark_wire_and_aliases_needed(wire_id, workspace);
                    }
                }
            }

            // Now that the reverse pass has converged for this pattern, the needed set precisely
            // describes which gate outputs are observable by effective outputs. Track constants
            // over only those observable patterns; values on unneeded patterns can be ignored
            // because downstream logic cannot see them for this input.
            self.track_observable_static_outputs(workspace);
            // self.export_wires(&wires);
        }

        let mut gates_to_comment = Vec::new();
        let mut assignments = Vec::new();
        let mut static_gates = Vec::new();
        let mut observably_static_gates = Vec::new();
        let mut arbitrary_gates = Vec::new();
        let mut used_gates = Vec::new();

        for (gate_idx, gate) in self.compiled_gates.iter().enumerate() {
            let gate_is_used = workspace.gates_impact_output[gate_idx];
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

            let output_was_needed = &workspace.output_was_needed[gate_idx];
            let no_outputs_needed = output_was_needed.iter().all(|&needed| !needed);
            let needed_static_values: Option<Vec<Bit>> = gate
                .outputs
                .iter()
                .enumerate()
                .map(|(output_idx, _)| {
                    if output_was_needed[output_idx] {
                        workspace.needed_output_is_static[gate_idx][output_idx]
                            .then_some(workspace.needed_static_output_values[gate_idx][output_idx])
                            .flatten()
                    } else {
                        Some(Bit::Low)
                    }
                })
                .collect();

            if no_outputs_needed {
                arbitrary_gates.push(gate.instance_name.clone());
                gates_to_comment.push(gate.instance_name.clone());

                for output in &gate.outputs {
                    assignments.push(GateOutputAssignment {
                        wire_name: output.wire_name.clone(),
                        value: Bit::Low,
                    });
                }
            } else if let Some(values) = static_values {
                static_gates.push(gate.instance_name.clone());
                gates_to_comment.push(gate.instance_name.clone());

                for (output, value) in gate.outputs.iter().zip(values) {
                    assignments.push(GateOutputAssignment {
                        wire_name: output.wire_name.clone(),
                        value,
                    });
                }
            } else if let Some(values) = needed_static_values {
                observably_static_gates.push(gate.instance_name.clone());
                gates_to_comment.push(gate.instance_name.clone());

                for (output, value) in gate.outputs.iter().zip(values) {
                    assignments.push(GateOutputAssignment {
                        wire_name: output.wire_name.clone(),
                        value,
                    });
                }
            } else if gate_is_used {
                used_gates.push(gate.instance_name.clone());
            }
        }

        GateUsageOptimization {
            used_gates,
            gates_to_comment,
            assignments,
            static_gates,
            observably_static_gates,
            arbitrary_gates,
        }
    }

    fn track_observable_static_outputs(&self, workspace: &mut OptimizationWorkspace) {
        for (gate_idx, gate) in self.compiled_gates.iter().enumerate() {
            for (output_idx, output) in gate.outputs.iter().enumerate() {
                let output_needed = output
                    .alias_wires
                    .iter()
                    .any(|&wire_id| self.wire_is_needed(wire_id, workspace));

                if !output_needed {
                    continue;
                }

                workspace.output_was_needed[gate_idx][output_idx] = true;

                if !workspace.needed_output_is_static[gate_idx][output_idx] {
                    continue;
                }

                let wire_id = output.alias_wires[0];
                let value = workspace.wires[wire_id].unwrap();

                if !matches!(value, Bit::Low | Bit::High) {
                    workspace.needed_output_is_static[gate_idx][output_idx] = false;
                    continue;
                }

                match workspace.needed_static_output_values[gate_idx][output_idx] {
                    Some(prev) if prev != value => {
                        workspace.needed_output_is_static[gate_idx][output_idx] = false;
                    }
                    Some(_) => {}
                    None => {
                        workspace.needed_static_output_values[gate_idx][output_idx] = Some(value);
                    }
                }
            }
        }
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

    fn apply_sequential_outputs(&self, wires: &mut [Option<Bit>]) {
        for &wire_id in &self.sequential_output_wires {
            write_wire_id_with_aliases(wires, &self.alias_wire_ids, wire_id, Bit::Var);
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

    fn wire_is_needed(&self, wire_id: WireId, workspace: &OptimizationWorkspace) -> bool {
        // Membership test for the current reverse-walk needed set. Old pattern markings have a
        // different generation number and therefore read as false.
        workspace.needed_generation[wire_id] == workspace.current_generation
    }

    fn wire_or_alias_is_needed(&self, wire_id: WireId, workspace: &OptimizationWorkspace) -> bool {
        // Aliased wires represent the same Verilog signal through continuous assigns, so any alias
        // being needed means this wire must also be treated as needed.
        self.wire_is_needed(wire_id, workspace)
            || self.alias_wire_ids[wire_id]
                .iter()
                .any(|&alias_id| self.wire_is_needed(alias_id, workspace))
    }

    fn mark_wire_and_aliases_needed(&self, wire_id: WireId, workspace: &mut OptimizationWorkspace) {
        // Mark by writing the current generation instead of inserting into a HashSet. This keeps
        // the inner reverse pass dense and lets `next_needed_generation` clear the set in O(1).
        workspace.needed_generation[wire_id] = workspace.current_generation;

        for &alias_id in &self.alias_wire_ids[wire_id] {
            workspace.needed_generation[alias_id] = workspace.current_generation;
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

fn read_sim_input(wires: &[Option<Bit>], input: &SimInput) -> Option<Bit> {
    match input {
        SimInput::Wire(id) => wires[*id],
        SimInput::Const(bit) => Some(*bit),
    }
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

    fn test_input(values: &[(&str, Bit)]) -> HashMap<String, Bit> {
        values
            .iter()
            .map(|(name, value)| ((*name).to_string(), *value))
            .collect()
    }

    #[test]
    fn optimize_marks_observably_static_output() {
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

        assert_eq!(optimization.static_gates, Vec::<String>::new());
        assert!(optimization
            .observably_static_gates
            .contains(&"g_and".to_string()));
        assert!(optimization.gates_to_comment.contains(&"g_and".to_string()));
        assert!(optimization.assignments.contains(&GateOutputAssignment {
            wire_name: "n0".to_string(),
            value: Bit::Low,
        }));
    }

    #[test]
    fn optimize_assigns_arbitrary_low_to_never_needed_output() {
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

        assert!(optimization
            .arbitrary_gates
            .contains(&"g_unused".to_string()));
        assert!(optimization
            .gates_to_comment
            .contains(&"g_unused".to_string()));
        assert!(optimization.assignments.contains(&GateOutputAssignment {
            wire_name: "unused".to_string(),
            value: Bit::Low,
        }));
        assert!(optimization.used_gates.contains(&"g_out".to_string()));
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
        assert!(optimization.used_gates.contains(&"g_buf".to_string()));
    }

    #[test]
    fn optimize_assigns_constants_for_mixed_needed_and_unneeded_outputs() {
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

        assert!(optimization
            .observably_static_gates
            .contains(&"g_dual".to_string()));
        assert!(optimization.assignments.contains(&GateOutputAssignment {
            wire_name: "n0".to_string(),
            value: Bit::Low,
        }));
        assert!(optimization.assignments.contains(&GateOutputAssignment {
            wire_name: "n1".to_string(),
            value: Bit::Low,
        }));
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
