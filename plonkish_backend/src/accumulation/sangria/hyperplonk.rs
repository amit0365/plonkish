// #[cfg(test)]
// pub(crate) mod test {
//     use crate::{
//         accumulation::{sangria::Sangria, test::run_accumulation_scheme},
//         backend::hyperplonk::{
//             //util::{rand_vanilla_plonk_circuit, rand_vanilla_plonk_with_lookup_circuit},
//             HyperPlonk,
//         },
//         pcs::{
//             multilinear::{Gemini, MultilinearIpa, MultilinearKzg}, // Zeromorph
//             univariate::UnivariateKzg,
//         },
//         util::{
//             test::{seeded_std_rng, std_rng},
//             transcript::Keccak256Transcript,
//             Itertools,
//         },
//     };
//     use halo2_proofs::halo2curves::{bn256::Bn256, grumpkin};
//     use std::iter;

//     macro_rules! tests {
//         ($name:ident, $pcs:ty, $num_vars_range:expr) => {
//             paste::paste! {
//                 #[test]
//                 fn [<$name _sangria_hyperplonk_vanilla_plonk>]() {
//                     run_accumulation_scheme::<_, Sangria<HyperPlonk<$pcs>>, Keccak256Transcript<_>, _>($num_vars_range, |num_vars| {
//                         let (circuit_info, _) = rand_vanilla_plonk_circuit(num_vars, std_rng(), seeded_std_rng());
//                         let circuits = iter::repeat_with(|| {
//                             let (_, circuit) = rand_vanilla_plonk_circuit(num_vars, std_rng(), seeded_std_rng());
//                             circuit
//                         }).take(3).collect_vec();
//                         (circuit_info, circuits)
//                     });
//                 }

//                 #[test]
//                 fn [<$name _sangria_hyperplonk_vanilla_plonk_with_lookup>]() {
//                     run_accumulation_scheme::<_, Sangria<HyperPlonk<$pcs>>, Keccak256Transcript<_>, _>($num_vars_range, |num_vars| {
//                         let (circuit_info, _) = rand_vanilla_plonk_with_lookup_circuit(num_vars, std_rng(), seeded_std_rng());
//                         let circuits = iter::repeat_with(|| {
//                             let (_, circuit) = rand_vanilla_plonk_with_lookup_circuit(num_vars, std_rng(), seeded_std_rng());
//                             circuit
//                         }).take(3).collect_vec();
//                         (circuit_info, circuits)
//                     });
//                 }
//             }
//         };
//         ($name:ident, $pcs:ty) => {
//             tests!($name, $pcs, 2..16);
//         };
//     }

//     tests!(ipa, MultilinearIpa<grumpkin::G1Affine>);
//     tests!(kzg, MultilinearKzg<Bn256>);
//     tests!(gemini_kzg, Gemini<UnivariateKzg<Bn256>>);
//     // tests!(zeromorph_kzg, Zeromorph<UnivariateKzg<Bn256>>);
// }
