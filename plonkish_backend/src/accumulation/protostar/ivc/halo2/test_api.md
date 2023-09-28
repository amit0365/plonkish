ak36@Amits-MacBook-Pro halo2 % cargo test --package plonkish_backend --lib --all-features --release -- accumulation::protostar::ivc::halo2::test::gemini_kzg_ipa_protostar_hyperplonk_ivc --exact --nocapture > test_log.log 2>&1

ak36@Amits-MacBook-Pro halo2 % cargo test --package plonkish_backend --lib --all-features --release -- accumulation::protostar::ivc::halo2::test::gemini_kzg_ipa_protostar_hyperplonk_ivc_with_aggregation --exact --nocapture > test_log_gemini_kzg_ipa_protostar_hyperplonk_ivc_with_aggregation.log 2>&1

pasta_curves = { version = "0.5.0", features = ["serde"] }
# Developer tooling dependencies
plotters = { version = "0.3.0", optional = true }
[features]
default = ["parallel", "frontend-halo2","dev-graph"]
dev-graph = ["plotters/bitmap_backend"]

pasta_curves = { path= "/Users/ak36/Desktop/han/pasta_curves-0.5.1"}
ff = { version = "0.13", features = ["bits"] }
group = "0.13"
