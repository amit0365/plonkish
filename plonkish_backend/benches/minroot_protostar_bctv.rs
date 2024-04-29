use halo2_base::gates::circuit::BaseCircuitParams;
use halo2_base::halo2_proofs::halo2curves::{bn256::{self, Bn256}, grumpkin};
use plonkish_backend::accumulation::protostar::ivc::halo2::test::{run_protostar_hyperplonk_ivc_minroot_preprocess, run_protostar_hyperplonk_ivc_prove};
use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use plonkish_backend::pcs::multilinear::{Gemini, MultilinearIpa};
use plonkish_backend::pcs::univariate::UnivariateKzg;

const NUM_VARS: usize = 19;
const NUM_STEPS: usize = 10;

fn bench_gemini_kzg_ipa_protostar_hyperplonk_ivc(c: &mut Criterion) {
    let circuit_params = BaseCircuitParams {
        k: NUM_VARS,
        num_advice_per_phase: vec![1],
        num_lookup_advice_per_phase: vec![1],
        num_fixed: 1,
        lookup_bits: Some(13),
        num_instance_columns: 1,
    };
    let (primary_circuit, secondary_circuit, ivc_pp, ivc_vp)
        = run_protostar_hyperplonk_ivc_minroot_preprocess::<
            bn256::G1Affine,
            Gemini<UnivariateKzg<Bn256>>,
            MultilinearIpa<grumpkin::G1Affine>,
        >(NUM_VARS, NUM_STEPS, circuit_params);
        
    let num_steps_values = vec![5, 10]; //, 100, 1000, 10000];
    let mut group = c.benchmark_group("Gemini KZG IPA Protostar HyperPlonk IVC");

    group.sample_size(10);

    for &num_steps in &num_steps_values {
        let test_name = BenchmarkId::new("entire_process", num_steps);
        
        group.bench_with_input(test_name, &num_steps, |b, &num_steps| {
            b.iter(|| {
                run_protostar_hyperplonk_ivc_prove(primary_circuit.clone(), secondary_circuit.clone(), ivc_pp.clone(), ivc_vp.clone(), NUM_VARS, num_steps);
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
