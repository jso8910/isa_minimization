use std::{collections::{HashMap, HashSet}, fs};

use petgraph::{algo::toposort, graph::{DiGraph, NodeIndex}};

use crate::{bit::{Bit, BitPattern}, parser::{Expr, ModuleNetlist, parse_netlist}, stdcell_library::{OutputPin, Pin, StandardCellLibrary}};

type WireId = usize;

#[derive(Debug, Clone)]
enum SimInput {
    Wire(WireId),
    Const(Bit),
}

#[derive(Debug, Clone)]
struct CompiledOutput {
    function: crate::bit::LookupTable,
    alias_wires: Vec<WireId>,
}

#[derive(Debug, Clone)]
struct CompiledGate {
    inputs: Vec<SimInput>,

    outputs: Vec<CompiledOutput>,
}

#[derive(Debug)]
pub struct Simulator {

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

impl Simulator {
    pub fn from_file(netlist_file: &str, standard_cell_file: &str) -> Self {
        let verilog = fs::read_to_string(netlist_file).unwrap();
        let netlist = parse_netlist(&verilog).unwrap();
        let cell_library = StandardCellLibrary::new(standard_cell_file).unwrap();

        let alias_map = build_alias_map(&netlist);
        let top_mod_outputs = compute_top_mod_outputs(&netlist, &alias_map);

        validate_instances(&netlist, &cell_library);

        let (graph, nodes) = build_dependency_graph(&netlist, &cell_library, &alias_map);
        let gate_sorted_order = sorted_gate_order(&graph);

        let (wire_ids, wire_names) = compile_wire_ids(&netlist);
        let alias_wire_ids = compile_alias_wire_ids(&alias_map, &wire_ids, wire_names.len());

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
            wire_ids,
            wire_names,
            alias_wire_ids,
            compiled_gates,

            sequential_output_wires,
            sequential_input_wires,
            constant_writes
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
                let value = read_sim_input(wires, input).unwrap_or_else(|| {
                    panic!("No simulated value for input {:?}", input)
                });

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

    fn apply_primary_inputs(
        &self,
        bit_input: &HashMap<String, Bit>,
        wires: &mut [Option<Bit>],
    ) {
        for (net_name, value) in bit_input {

            let wire_id = *self
                .wire_ids
                .get(net_name)
                .unwrap_or_else(|| panic!("Unknown primary input net {}", net_name));

            write_wire_id_with_aliases(
                wires,
                &self.alias_wire_ids,
                wire_id,
                *value,
            );
        }
    }

    fn apply_sequential_outputs(&self, wires: &mut [Option<Bit>]) {
        for &wire_id in &self.sequential_output_wires {
            write_wire_id_with_aliases(
                wires,
                &self.alias_wire_ids,
                wire_id,
                Bit::Var,
            );
        }
    }

    fn mark_sequential_inputs_nonarbitrary(
        &self,
        wires_nonarbitrary: &mut HashSet<WireId>,
    ) {
        for &wire_id in &self.sequential_input_wires {
            self.mark_wire_and_aliases_nonarbitrary(wire_id, wires_nonarbitrary);
        }
    }

    fn apply_constant_assigns(&self, wires: &mut [Option<Bit>]) {
        for &(wire_id, value) in &self.constant_writes {
            write_wire_id_with_aliases(
                wires,
                &self.alias_wire_ids,
                wire_id,
                value,
            );
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
                result.insert(
                    self.wire_names[wire_id].clone(),
                    *value,
                );
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
    alias_map: &HashMap<Expr, HashSet<String>>,
) -> Vec<String> {
    let mut top_mod_outputs_set: HashSet<String> =
        netlist.outputs.iter().cloned().collect();

    for (source, dests) in alias_map {
        let Expr::Net(source_name) = source else {
            continue;
        };

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

fn build_dependency_graph(netlist: &ModuleNetlist, cell_library: &StandardCellLibrary, alias_map: &HashMap<Expr, HashSet<String>>) -> (DiGraph<String, ()>, HashMap<String, NodeIndex>) {
    // create graph
    let mut graph = DiGraph::new();
    let mut nodes = HashMap::new();

    // Iterate through to create nodes
    for (instance_name, inst) in netlist.instances.iter() {
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
    (graph, nodes)
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
            panic!("Graph has a cycle! Cannot sort! Cycle starts at {:?}", cycle.node_id());
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

fn compile_alias_wire_ids (alias_map: &HashMap<Expr, HashSet<String>>, wire_ids: &HashMap<String, usize>, num_wires: usize) -> Vec<Vec<usize>> {
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

        let value = parse_one_bit_const(c)
            .unwrap_or_else(|| panic!("Unsupported assigned constant {}", c));

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
    alias_wire_ids: &Vec<Vec<usize>>
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
                    function: out_pin.function.clone(),
                    alias_wires: alias_wire_ids[out_id].clone(),
                });
            }
        }

        compiled_gates.push(CompiledGate {
            inputs,
            outputs,
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

use super::*;
    #[test]
    fn alu_sim_test() {
        let simulator = Simulator::from_file("examples/alu_syn.v", "examples/NangateOpenCellLibrary_typical.lib");
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
                    _ => panic!("How?")
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
                        _ => panic!("How?")
                    };
                    bit_input.insert(format!("b[{}]", bit_idx), bit);
                }
                let wires = simulator.simulate(&bit_input, &mut wires_nonarbitrary);
                let output_val: u8 = (0..=7)
                    .map(|i| {
                        match wires.get(&format!("out[{i}]")).unwrap() {
                            Bit::High => 1 << i,
                            Bit::Low => 0,
                            _ => panic!("Output should not have any variable or test bits!")
                        }
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