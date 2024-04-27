use plonkish_backend::accumulation::protostar::ivc::halo2::test::{gemini_kzg_ipa_protostar_hyperplonk_ivc_bench, run_protostar_hyperplonk_ivc};
use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};

fn bench_gemini_kzg_ipa_protostar_hyperplonk_ivc(c: &mut Criterion) {
    let num_steps_values = vec![5, 10];//, 100, 1000, 10000];
    let mut group = c.benchmark_group("Gemini KZG IPA Protostar HyperPlonk IVC");

    group.sample_size(10);

    for &num_steps in &num_steps_values {
        let test_name = BenchmarkId::new("entire_process", num_steps);
        
        group.bench_with_input(test_name, &num_steps, |b, &num_steps| {
            b.iter(|| {
                gemini_kzg_ipa_protostar_hyperplonk_ivc_bench(num_steps);
            });
        });
    }

    group.finish();
}

fn minroot_protostar_bctv(c: &mut Criterion) {
    bench_gemini_kzg_ipa_protostar_hyperplonk_ivc(c);
}

criterion_group!(benches, minroot_protostar_bctv);
criterion_main!(benches);
