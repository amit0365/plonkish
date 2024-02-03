use plonkish_backend::accumulation::protostar::ivc::halo2::test::{gemini_kzg_ipa_protostar_hyperplonk_ivc, run_protostar_hyperplonk_ivc};
use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};

fn bench_gemini_kzg_ipa_protostar_hyperplonk_ivc(c: &mut Criterion) {
    let num_steps_values = vec![3, 10];//, 100, 1000, 10000];
    let mut group = c.benchmark_group("Gemini KZG IPA Protostar HyperPlonk IVC");

    group.sample_size(10);

    for &num_steps in &num_steps_values {
        let test_name = BenchmarkId::new("entire_process", num_steps);
        
        group.bench_with_input(test_name, &num_steps, |b, &num_steps| {
            b.iter(|| {
                gemini_kzg_ipa_protostar_hyperplonk_ivc(num_steps);
            });
        });
    }

    group.finish();
}

fn ivc(c: &mut Criterion) {
    bench_gemini_kzg_ipa_protostar_hyperplonk_ivc(c);
}

criterion_group!(benches, ivc);
criterion_main!(benches);

// fn bench_gemini_kzg_ipa_protostar_hyperplonk_ivc(c: &mut Criterion) {
//     let num_steps = vec![10, 100, 1000, 10000];
//     c.bench_function("entire_process", |b| {
//         b.iter(|| {
//             gemini_kzg_ipa_protostar_hyperplonk_ivc(num_steps);
//         });
//     });
// }