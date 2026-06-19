use criterion::{Criterion, black_box, criterion_group, criterion_main};
use std::collections::{HashMap, HashSet};

use isa_minimization::{bit::Bit, parser::Expr, simulator::Simulator};

fn make_input() -> HashMap<String, Bit> {
    let mut bit_input = HashMap::new();

    for i in 0..8 {
        bit_input.insert(format!("a0_mux[{i}]"), Bit::Low);
        bit_input.insert(format!("a1_mux[{i}]"), Bit::Low);
        bit_input.insert(format!("b[{i}]"), Bit::Low);
    }

    bit_input.insert("a_sel".into(), Bit::Low);
    bit_input.insert("sel".into(), Bit::Low);
    bit_input.insert("ctrl[2]".into(), Bit::Low);
    bit_input.insert("ctrl[1]".into(), Bit::Low);
    bit_input.insert("ctrl[0]".into(), Bit::Low);

    bit_input
}

fn bench_simulate(c: &mut Criterion) {
    let simulator = Simulator::from_file(
        "examples/alu_syn.v",
        "examples/NangateOpenCellLibrary_typical.lib",
    );

    let bit_input = make_input();

    c.bench_function("simulate", |b| {
        b.iter(|| {
            let mut wires_nonarbitrary = HashSet::new();

            black_box(
                simulator.simulate(black_box(&bit_input), black_box(&mut wires_nonarbitrary)),
            );
        });
    });
}

criterion_group!(benches, bench_simulate);
criterion_main!(benches);
