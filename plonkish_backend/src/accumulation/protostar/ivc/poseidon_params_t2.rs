//! This file was generated by running generate_params.py
//! Number of round constants: 128
//! Round constants for GF(p):
//! Parameters for using rate 1 Poseidon with the BN256 field.
//! Patterned after [halo2_gadgets::poseidon::primitives::fp]
//! The parameters can be reproduced by running the following Sage script from
//! [this repository](https://github.com/daira/pasta-hadeshash):
//!
//! ```text
//! $ sage generate_parameters_grain.sage 1 0 254 2 8 56 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001 --rust
//! ```
//!
//! where 1 means 'prime field', 0 means 'non-negative sbox', 254 is the bitsize
//! of the field, 2 is the Poseidon width (rate + 1), 8 is the number of full
//! rounds, 56 is the number of partial rounds.
//! More info here => https://hackmd.io/@letargicus/SJOvx48Nn
use halo2_base::halo2_proofs::halo2curves::bn256::Fr as Fp;
pub(crate) const ROUND_CONSTANTS: [[Fp; 2]; 64] = [
    [
        Fp::from_raw([
            0x6c7d_c0db_d0ab_d7a7,
            0xa71a_a177_534c_dd1b,
            0xfe1f_aaba_294c_ba38,
            0x09c4_6e9e_c68e_9bd4,
        ]),
        Fp::from_raw([
            0x3c1d_83ff_a604_cb81,
            0xc514_2b3a_e405_b834,
            0x2a97_ed93_7f31_35cf,
            0x0c03_5653_0896_eec4,
        ]),
    ],
    [
        Fp::from_raw([
            0x317e_a977_cc15_4a30,
            0xa00e_a5aa_bd62_68bd,
            0x142e_5118_2bb5_4cf4,
            0x1e28_a1d9_3569_8ad1,
        ]),
        Fp::from_raw([
            0x4cf9_e2b1_2b91_251f,
            0x0e57_57c3_e008_db96,
            0x0809_65db_30e2_98e4,
            0x27af_2d83_1a9d_2748,
        ]),
    ],
    [
        Fp::from_raw([
            0x79aa_f435_45b7_4e03,
            0x4129_1462_f214_cd08,
            0x3a6a_3cfe_16ae_175a,
            0x1e6f_11ce_60fc_8f51,
        ]),
        Fp::from_raw([
            0xf719_2062_68d1_42d3,
            0x0446_2ed1_4c36_13d8,
            0x8541_819c_b681_f0be,
            0x2a67_384d_3bbd_5e43,
        ]),
    ],
    [
        Fp::from_raw([
            0x3640_8f5d_5c9f_45d0,
            0xb985_e381_f025_1889,
            0x1609_f8e1_2fbf_ecf0,
            0x0b66_fdf3_5609_3a61,
        ]),
        Fp::from_raw([
            0xdaa6_852d_bdb0_9e21,
            0x0b26_c83c_c5ce_beed,
            0x830c_6109_3c2a_de37,
            0x012e_e3ec_1e78_d470,
        ]),
    ],
    [
        Fp::from_raw([
            0x2d10_8e7b_445b_b1b9,
            0x6cd1_c431_b099_b6bb,
            0xfd88_f67f_8175_e3fd,
            0x0252_ba5f_6760_bfbd,
        ]),
        Fp::from_raw([
            0xef5a_eaad_7ca9_32f1,
            0x5439_1a89_35ff_71d6,
            0x6c6b_ec3c_ef54_2963,
            0x1794_74cc_eca5_ff67,
        ]),
    ],
    [
        Fp::from_raw([
            0x7e1a_2589_bbed_2b91,
            0x9c1f_974a_2649_69b3,
            0x9228_ff4a_503f_d4ed,
            0x2c24_2613_79a5_1bfa,
        ]),
        Fp::from_raw([
            0x53e6_6c05_5180_1b05,
            0xc2f6_3f50_01fc_0fc5,
            0xac2f_288b_d069_5b43,
            0x1cc1_d7b6_2692_e63e,
        ]),
    ],
    [
        Fp::from_raw([
            0x5d9e_ff5f_d9c9_1b56,
            0x0078_4dbf_17fb_acd0,
            0xb2ed_55f8_5297_9e96,
            0x2550_5930_1aad_a98b,
        ]),
        Fp::from_raw([
            0xb11c_29ce_7e59_efd9,
            0xaea2_4234_970a_8193,
            0x79e1_f5c0_eccd_32b3,
            0x2843_7be3_ac1c_b2e4,
        ]),
    ],
    [
        Fp::from_raw([
            0x3387_62c3_7f5f_2043,
            0x1854_8da8_fb4f_78d4,
            0x1ca4_fa6b_5376_6eb1,
            0x2821_6a44_2f2e_1f71,
        ]),
        Fp::from_raw([
            0x131f_2377_3234_82c9,
            0xeee1_efce_0309_4581,
            0x1f39_f4e7_056d_d03f,
            0x2c1f_47cd_17fa_5adf,
        ]),
    ],
    [
        Fp::from_raw([
            0x646b_8566_a621_afc9,
            0xd9da_fca2_7663_8a63,
            0x8632_bcc9_356c_eb7d,
            0x07ab_ad02_b7a5_ebc4,
        ]),
        Fp::from_raw([
            0x37da_0c4d_15f9_6c3c,
            0x9429_f908_80a6_9cd1,
            0x275b_33ff_aab5_1dfe,
            0x0230_2646_01ff_df29,
        ]),
    ],
    [
        Fp::from_raw([
            0x717e_5d66_899a_a0a9,
            0xa864_4145_57ee_289e,
            0xa0f1_6865_6497_ca40,
            0x1bc9_7305_4e51_d905,
        ]),
        Fp::from_raw([
            0x2a6b_2228_8f0a_67fc,
            0xd249_aff5_c2d8_421f,
            0x206c_3157_e863_41ed,
            0x2e1c_22f9_6443_5008,
        ]),
    ],
    [
        Fp::from_raw([
            0xa704_52bc_2bba_86b8,
            0x9e8e_a159_8e46_c9f7,
            0x121c_1d5f_461b_bc50,
            0x1224_f38d_f67c_5378,
        ]),
        Fp::from_raw([
            0x69d2_9891_86cd_e20e,
            0xd7bf_e8cd_9dfe_da19,
            0x9280_b4bd_9ed0_068f,
            0x02e4_e69d_8ba5_9e51,
        ]),
    ],
    [
        Fp::from_raw([
            0x6d47_e973_5d98_018e,
            0x4f19_ee36_4e65_3f07,
            0x7f5d_f81f_c04f_f3ee,
            0x1f1e_ccc3_4aab_a013,
        ]),
        Fp::from_raw([
            0xeacb_8a4d_4284_f582,
            0x1424_4480_32cd_1819,
            0x7426_6c30_39a9_a731,
            0x1672_ad3d_709a_3539,
        ]),
    ],
    [
        Fp::from_raw([
            0x1d2e_d602_df8c_8fc7,
            0xcda6_961f_284d_2499,
            0x56f4_4af5_192b_4ae9,
            0x283e_3fdc_2c6e_420c,
        ]),
        Fp::from_raw([
            0x614f_bd69_ff39_4bcc,
            0x6837_51f8_fdff_59d6,
            0xd0db_0957_170f_a013,
            0x1c2a_3d12_0c55_0ecf,
        ]),
    ],
    [
        Fp::from_raw([
            0x96cb_6b81_7765_3fbd,
            0x143a_9a43_773e_a6f2,
            0xf789_7a73_2345_6efe,
            0x216f_8487_7aac_6172,
        ]),
        Fp::from_raw([
            0x11a1_f515_52f9_4788,
            0xceaa_47ea_61ca_59a4,
            0x64ba_7e8e_3e28_d12b,
            0x2c0d_272b_ecf2_a757,
        ]),
    ],
    [
        Fp::from_raw([
            0xcb4a_6c3d_8954_6f43,
            0x170a_5480_abe0_508f,
            0x484e_e7a7_4c45_4e9f,
            0x16e3_4299_865c_0e28,
        ]),
        Fp::from_raw([
            0x48cd_9397_5548_8fc5,
            0x7720_4776_5802_290f,
            0x375a_232a_6fb9_cc71,
            0x175c_eba5_99e9_6f5b,
        ]),
    ],
    [
        Fp::from_raw([
            0xd8c5_ffbb_44a1_ee32,
            0x6aa4_10bf_bc35_4f54,
            0xfead_9e17_58b0_2806,
            0x0c75_9444_0dc4_8c16,
        ]),
        Fp::from_raw([
            0x9247_9882_d919_fd8d,
            0x760e_2001_3ccf_912c,
            0xc466_db7d_7eb6_fd8f,
            0x1a3c_29bc_39f2_1bb5,
        ]),
    ],
    [
        Fp::from_raw([
            0x95c8_eeab_cd22_e68f,
            0x0855_d349_074f_5a66,
            0xc098_6ea0_49b2_5340,
            0x0ccf_dd90_6f34_26e5,
        ]),
        Fp::from_raw([
            0xe0e6_99b6_7dd9_e796,
            0x66a7_a8a3_fd06_5b3c,
            0x2bdb_475c_e6c9_4118,
            0x14f6_bc81_d9f1_86f6,
        ]),
    ],
    [
        Fp::from_raw([
            0x88ed_eb73_86b9_7052,
            0xcc09_9810_c9c4_95c8,
            0x9702_ca70_b2f6_c5aa,
            0x0962_b827_89fb_3d12,
        ]),
        Fp::from_raw([
            0xafef_0c8f_6a31_a86d,
            0x1328_4ab0_1ef0_2575,
            0xbf20_c79d_e251_27bc,
            0x1a88_0af7_074d_18b3,
        ]),
    ],
    [
        Fp::from_raw([
            0x4c30_12bb_7ae9_311b,
            0x20af_2924_fc20_ff3f,
            0xcd5e_77f0_211c_154b,
            0x10cb_a184_19a6_a332,
        ]),
        Fp::from_raw([
            0x756a_2849_f302_f10d,
            0xfa27_b731_9cae_3406,
            0xbdc7_6ba6_3a9e_aca8,
            0x057e_62a9_a8f8_9b3e,
        ]),
    ],
    [
        Fp::from_raw([
            0xafa0_413b_4428_0cee,
            0xb961_303b_bf65_cff5,
            0xd44a_df53_84b4_988c,
            0x287c_971d_e91d_c0ab,
        ]),
        Fp::from_raw([
            0x6f7f_7960_e306_891d,
            0x1e56_2bc4_6d4a_ba4e,
            0xb3bc_a9da_0cca_908f,
            0x21df_3388_af16_87bb,
        ]),
    ],
    [
        Fp::from_raw([
            0x3eff_8b56_0e16_82b3,
            0x789d_f8f7_0b49_8fd8,
            0x3e25_cc97_4d09_34cd,
            0x1be5_c887_d25b_ce70,
        ]),
        Fp::from_raw([
            0x48d5_9c27_06a0_d5c1,
            0xd2cb_5d42_fda5_acea,
            0x6811_7175_cea2_cd0d,
            0x268d_a36f_76e5_68fb,
        ]),
    ],
    [
        Fp::from_raw([
            0xbd06_460c_c26a_5ed6,
            0xc5d8_bb74_135e_bd05,
            0xc609_beaf_5510_ecec,
            0x0e17_ab09_1f6e_ae50,
        ]),
        Fp::from_raw([
            0x040f_5caa_1f62_af40,
            0x91ef_62d8_cf83_d270,
            0x7aee_535a_b074_a430,
            0x04d7_27e7_28ff_a0a6,
        ]),
    ],
    [
        Fp::from_raw([
            0x2b15_417d_7e39_ca6e,
            0x3370_2ac1_0f1b_fd86,
            0x81b5_4976_2bc0_22ed,
            0x0ddb_d7bf_9c29_3415,
        ]),
        Fp::from_raw([
            0x8a29_c49c_8789_654b,
            0x34f5_b0d1_d3af_9b58,
            0x7681_62e8_2989_c6c2,
            0x2790_eb33_5162_1752,
        ]),
    ],
    [
        Fp::from_raw([
            0x84b7_6420_6142_f9e9,
            0x395f_3d9a_b8b2_fd09,
            0x4471_9501_93d8_a570,
            0x1e45_7c60_1a63_b73e,
        ]),
        Fp::from_raw([
            0xc4c6_86fc_46e0_91b0,
            0xfa90_ecd0_c43f_f91f,
            0x638d_6ab2_bbe7_135f,
            0x21ae_6430_1dca_9625,
        ]),
    ],
    [
        Fp::from_raw([
            0x5858_534e_ed8d_350b,
            0x854b_e9e3_432e_0955,
            0x4da2_9316_6f49_4928,
            0x0379_f63c_8ce3_468d,
        ]),
        Fp::from_raw([
            0x8c9f_58a3_24c3_5049,
            0xca0e_4921_a466_86ac,
            0x6a74_4a08_0809_e054,
            0x002d_5642_0359_d026,
        ]),
    ],
    [
        Fp::from_raw([
            0x0fc2_c5af_9635_15a6,
            0xda8d_6245_9e21_f409,
            0x1d68_b3cd_32e1_0bbe,
            0x1231_58e5_965b_5d9b,
        ]),
        Fp::from_raw([
            0x60c8_0eb4_9cad_9ec1,
            0x0fbb_2b6f_5283_6d4e,
            0x661d_14bb_f6cb_e042,
            0x0be2_9fc4_0847_a941,
        ]),
    ],
    [
        Fp::from_raw([
            0x2338_02f2_4fdf_4c1a,
            0x36db_9d85_9cad_5f9a,
            0x5771_6142_015a_453c,
            0x1ac9_6991_dec2_bb05,
        ]),
        Fp::from_raw([
            0x51ca_3355_bcb0_627e,
            0x5e12_c9fa_97f1_8a92,
            0x5f49_64fc_61d2_3b3e,
            0x1596_443f_763d_bcc2,
        ]),
    ],
    [
        Fp::from_raw([
            0xd6d0_49ea_e3ba_3212,
            0xf185_7d9f_17e7_15ae,
            0x6b28_61d4_ec3a_eae0,
            0x12e0_bcd3_654b_dfa7,
        ]),
        Fp::from_raw([
            0x04e6_c76c_7cf9_64ba,
            0xceab_ac7f_3715_4b19,
            0x9ea7_3d4a_f9af_2a50,
            0x0fc9_2b4f_1bbe_a82b,
        ]),
    ],
    [
        Fp::from_raw([
            0x9c7e_9652_3387_2762,
            0xb14f_7c77_2223_6f4f,
            0xd6f2_e592_a801_3f40,
            0x1f9c_0b16_1044_6442,
        ]),
        Fp::from_raw([
            0x8d15_9f64_3dbb_f4d3,
            0x050d_914d_a38b_4c05,
            0xf8cd_e061_57a7_82f4,
            0x0ebd_7424_4ae7_2675,
        ]),
    ],
    [
        Fp::from_raw([
            0x7a83_9839_dccf_c6d1,
            0x3b06_71e9_7346_ee39,
            0x69a9_fafd_4ab9_51c0,
            0x2cb7_f0ed_39e1_6e9f,
        ]),
        Fp::from_raw([
            0x90c7_2bca_7352_d9bf,
            0xce76_1d05_14ce_5266,
            0x5605_443e_e41b_ab20,
            0x1a9d_6e2e_cff0_22cc,
        ]),
    ],
    [
        Fp::from_raw([
            0x87da_182d_648e_c72f,
            0xd0c1_3326_a9a7_ba30,
            0x5ea8_3c3b_c44a_9331,
            0x2a11_5439_607f_335a,
        ]),
        Fp::from_raw([
            0x9535_c115_c5a4_c060,
            0xe738_b563_05cd_44f2,
            0x15b8_fa7a_ee3e_3410,
            0x23f9_b652_9b5d_040d,
        ]),
    ],
    [
        Fp::from_raw([
            0x260e_b939_f0e6_e8a7,
            0xa3ce_97c1_6d58_b68b,
            0x249a_c6ba_484b_b9c3,
            0x0587_2c16_db0f_72a2,
        ]),
        Fp::from_raw([
            0x2b62_4a7c_dedd_f6a7,
            0x0219_b615_1d55_b5c5,
            0xca20_fb80_1180_75f4,
            0x1300_bdee_08bb_7824,
        ]),
    ],
    [
        Fp::from_raw([
            0x072e_4e7b_7d52_b376,
            0x8d7a_d299_16d9_8cb1,
            0xe638_1786_3a8f_6c28,
            0x19b9_b63d_2f10_8e17,
        ]),
        Fp::from_raw([
            0x24a2_0128_481b_4f7f,
            0x13d1_c887_26b5_ec42,
            0xb5bd_a237_6685_22f6,
            0x015b_ee13_57e3_c015,
        ]),
    ],
    [
        Fp::from_raw([
            0xea92_c785_b128_ffd1,
            0xfe1e_1ce4_bab2_18cb,
            0x1b97_07a4_f161_5e4e,
            0x2953_736e_94bb_6b9f,
        ]),
        Fp::from_raw([
            0x4ce7_266e_d660_8dfc,
            0x851b_98d3_72b4_5f54,
            0x862f_8061_80c0_385f,
            0x0b06_9353_ba09_1618,
        ]),
    ],
    [
        Fp::from_raw([
            0x4f58_8ac9_7d81_f429,
            0x55ae_b7eb_9306_b64e,
            0x15e4_e0bc_fb93_817e,
            0x304f_74d4_61cc_c131,
        ]),
        Fp::from_raw([
            0xb8ee_5415_cde9_13fc,
            0xaad2_a164_a461_7a4c,
            0xe8a3_3f5e_77df_e4f5,
            0x15bb_f146_ce9b_ca09,
        ]),
    ],
    [
        Fp::from_raw([
            0xa9ff_2385_9572_c8c6,
            0x9b8f_4b85_0405_c10c,
            0x4490_1031_4879_64ed,
            0x0ab4_dfe0_c274_2cde,
        ]),
        Fp::from_raw([
            0x251d_e39f_9639_779a,
            0xef5e_edfe_a546_dea9,
            0x97f4_5f76_49a1_9675,
            0x0e32_db32_0a04_4e31,
        ]),
    ],
    [
        Fp::from_raw([
            0xa307_8efa_516d_a016,
            0x6797_733a_8277_4896,
            0xb276_35a7_8b68_88e6,
            0x0a17_56aa_1f37_8ca4,
        ]),
        Fp::from_raw([
            0x4254_d6a2_a25d_93ef,
            0x95e6_1d32_8f85_efa9,
            0x47fd_1717_7f95_2ef8,
            0x044c_4a33_b10f_6934,
        ]),
    ],
    [
        Fp::from_raw([
            0xd37b_07b5_466c_4b8b,
            0xfe08_79d7_9a49_6891,
            0xbe65_5b53_7f66_f700,
            0x2ed3_611b_725b_8a70,
        ]),
        Fp::from_raw([
            0xd833_9ea7_1208_58aa,
            0xadfd_eb9c_fdd3_47b5,
            0xc8ec_c3d7_22aa_2e0e,
            0x1f9b_a4e8_bab7_ce42,
        ]),
    ],
    [
        Fp::from_raw([
            0xb740_56f8_65c5_d3da,
            0xa38e_82ac_4502_066d,
            0x8f7e_e907_a84e_518a,
            0x1b23_3043_052e_8c28,
        ]),
        Fp::from_raw([
            0xca2f_97b0_2087_5954,
            0x9020_53bf_c0f1_4db0,
            0x7403_1ab7_2bd5_5b4c,
            0x2431_e1cc_164b_b8d0,
        ]),
    ],
    [
        Fp::from_raw([
            0xa791_f273_9658_01fd,
            0xa13e_3220_9758_3319,
            0x30cd_6953_a0a7_db45,
            0x082f_934c_91f5_aac3,
        ]),
        Fp::from_raw([
            0x9ad6_bb93_0c48_997c,
            0xc772_45e2_ae7c_be99,
            0xa34b_e074_3155_42a3,
            0x2b9a_0a22_3e75_38b0,
        ]),
    ],
    [
        Fp::from_raw([
            0xb0b5_89cc_7021_4e7d,
            0x8164_163e_75a8_a00e,
            0xceb8_5483_b887_a9be,
            0x0e1c_d91e_dd2c_fa2c,
        ]),
        Fp::from_raw([
            0x88d3_2460_1ceb_e2f9,
            0x9977_4f19_854d_00f5,
            0xc951_f614_77e3_6989,
            0x2e1e_ac0f_2bfd_fd63,
        ]),
    ],
    [
        Fp::from_raw([
            0x23d7_4811_5b50_0b83,
            0x7345_784d_8efd_b33c,
            0x0c76_158e_769d_6d15,
            0x0cbf_a95f_37fb_7406,
        ]),
        Fp::from_raw([
            0x980c_232d_fa4a_4f84,
            0x76d9_91e3_a775_13d9,
            0xd65a_d49d_8a61_e9a6,
            0x08f0_5b3b_e923_ed44,
        ]),
    ],
    [
        Fp::from_raw([
            0x25a2_dd51_0c04_7ef6,
            0xe728_4925_dc07_58a3,
            0x52bf_8e21_984d_0443,
            0x2271_9e2a_070b_cd08,
        ]),
        Fp::from_raw([
            0xf41f_62b2_f268_30c0,
            0x7bdb_f036_1199_82c0,
            0xc060_f7fc_c3a1_ab4c,
            0x041f_596a_9ee1_cb2b,
        ]),
    ],
    [
        Fp::from_raw([
            0x19fc_dd09_86b1_0f89,
            0x021b_e1c2_d0dc_464a,
            0x8762_8eb0_6f6b_1d4c,
            0x233f_d35d_e1be_520a,
        ]),
        Fp::from_raw([
            0xefcb_453c_61c9_c267,
            0xd31e_078a_a1b4_707e,
            0x4325_e0a4_23eb_c810,
            0x0524_b46d_1aa8_7a5e,
        ]),
    ],
    [
        Fp::from_raw([
            0xcc44_8623_7c51_5211,
            0x4227_bb95_4b0f_3199,
            0xce47_fcac_894b_8582,
            0x2c34_f424_c81e_5716,
        ]),
        Fp::from_raw([
            0xf330_1032_7de4_915e,
            0x2dd2_025b_5457_cc97,
            0x207e_ffc2_b554_1fb7,
            0x0b5f_2a4b_6338_7819,
        ]),
    ],
    [
        Fp::from_raw([
            0xaefa_c41f_e05c_659f,
            0xc174_35d2_f57a_f6ce,
            0xc5b7_2fe4_39d2_cfd6,
            0x2220_7856_082c_cc54,
        ]),
        Fp::from_raw([
            0x2785_4048_ce2c_8171,
            0xcdfb_2101_94ca_f79f,
            0x4e24_159b_7f89_50b5,
            0x24d5_7a8b_f5da_63fe,
        ]),
    ],
    [
        Fp::from_raw([
            0x7391_9bb2_3b79_396e,
            0x374a_d709_7bb0_1a85,
            0x3b37_1d75_bd69_3f98,
            0x0afa_b181_fdd5_e058,
        ]),
        Fp::from_raw([
            0xf162_90d6_2b11_28ee,
            0x76c0_0571_94c1_6c0b,
            0x998a_52ef_ac7c_bd56,
            0x2dba_9b10_8f20_8772,
        ]),
    ],
    [
        Fp::from_raw([
            0x5aff_13e6_bce4_20b3,
            0xcbb8_3de0_bd59_2b25,
            0x56f8_81c7_88f5_3f83,
            0x2634_9b66_edb8_b16f,
        ]),
        Fp::from_raw([
            0x2352_88a3_e6f1_37db,
            0xd81a_56d2_8ecc_193b,
            0x685e_95f9_2339_753a,
            0x25af_7ce0_e5e1_0357,
        ]),
    ],
    [
        Fp::from_raw([
            0x1f7c_0187_fe35_011f,
            0x70ee_d7aa_e88b_2bff,
            0xc094_d6a5_5edd_68b9,
            0x25b4_ce7b_d229_4390,
        ]),
        Fp::from_raw([
            0x8cb9_d54c_1e02_b631,
            0xde9c_ef28_ebdf_30b1,
            0x387e_53f1_908a_88e5,
            0x22c5_43f1_0f6c_89ec,
        ]),
    ],
    [
        Fp::from_raw([
            0xdf66_8e74_882f_87a9,
            0x425e_906a_919d_7a34,
            0x4fc7_908a_9f19_1e1e,
            0x0236_f93e_7789_c472,
        ]),
        Fp::from_raw([
            0x9cb4_97af_980c_4b52,
            0x652b_dae1_14eb_0165,
            0x0e7d_27e3_7d05_da99,
            0x2935_0b40_1166_ca01,
        ]),
    ],
    [
        Fp::from_raw([
            0xee12_6091_6652_363f,
            0x65ed_b75d_844e_bb89,
            0x6bd3_1bba_b547_f75a,
            0x0eed_787d_6582_0d3f,
        ]),
        Fp::from_raw([
            0x1906_f656_f4de_6fad,
            0xfdcd_0e99_bd94_297d,
            0x036a_753f_520b_3291,
            0x07cc_1170_f13b_46f2,
        ]),
    ],
    [
        Fp::from_raw([
            0x2059_4356_89e8_acea,
            0x9087_86d7_f9f5_d10c,
            0xf49b_cf61_3a3d_30b1,
            0x22b9_3923_3b1d_7205,
        ]),
        Fp::from_raw([
            0xadd6_50ac_e60a_e5a6,
            0x740f_083a_5aa8_5438,
            0x8aad_1dc8_bc33_e870,
            0x0145_1762_a0aa_b81c,
        ]),
    ],
    [
        Fp::from_raw([
            0xe704_fec0_892f_ce89,
            0xe32e_aa61_dec7_da57,
            0x61fa_bf10_25d4_6d1f,
            0x2350_6bb5_d872_7d44,
        ]),
        Fp::from_raw([
            0x7f8b_d689_0735_5522,
            0x2a37_0953_1e1e_fea9,
            0xbac0_6ae3_f71b_dd09,
            0x2e48_4c44_e838_aea0,
        ]),
    ],
    [
        Fp::from_raw([
            0x4541_8da2_6835_b54c,
            0xaf4a_5945_45ce_dc25,
            0x379e_78c5_0bd2_e42b,
            0x0f4b_c7d0_7eba_fd64,
        ]),
        Fp::from_raw([
            0xe620_996d_50d8_e74e,
            0x5158_2388_725d_f460,
            0xfa76_6378_62fa_aee8,
            0x1f4d_3c8f_6583_e9e5,
        ]),
    ],
    [
        Fp::from_raw([
            0x53eb_9bcb_48fe_7389,
            0xfae0_2abc_7b68_1d91,
            0x2660_d07b_e0e4_a988,
            0x0935_14e0_c707_11f8,
        ]),
        Fp::from_raw([
            0x4a58_e0a3_47e1_53d8,
            0x43ee_83ec_e472_28f2,
            0x4669_9a2b_5f3b_c036,
            0x1ada_b0c8_e2b3_bad3,
        ]),
    ],
    [
        Fp::from_raw([
            0x1a22_dbef_9e80_dad2,
            0x378c_1b94_b807_2bac,
            0xd147_09eb_b474_641a,
            0x1672_b172_6057_d99d,
        ]),
        Fp::from_raw([
            0x30d4_7b23_9b47_9c14,
            0xc5d8_e2fa_e0ac_c4ee,
            0x8f44_f53f_dcab_468c,
            0x1dfd_53d4_576a_f2e3,
        ]),
    ],
    [
        Fp::from_raw([
            0xbc7f_2077_5320_5c60,
            0xe6d7_7d64_0f6f_c3de,
            0xa70a_3626_3a37_e17f,
            0x0c68_88a1_0b75_b0f3,
        ]),
        Fp::from_raw([
            0x8509_1ecc_a9d1_e508,
            0x611a_61e0_0ee6_848b,
            0x92b3_4a7e_77d1_2fe8,
            0x1add_b933_a65b_e770,
        ]),
    ],
    [
        Fp::from_raw([
            0x7935_628e_299d_1791,
            0xf638_ff54_25f0_afff,
            0x5c10_ae18_d1de_933c,
            0x00d7_540d_cd26_8a84,
        ]),
        Fp::from_raw([
            0xd316_939d_20b8_2c0e,
            0x26fe_dde4_acd9_9db1,
            0x01b2_827a_5664_ca9c,
            0x140c_0e42_687e_9ead,
        ]),
    ],
    [
        Fp::from_raw([
            0xc091_e2ae_5656_5984,
            0xc20a_0f9b_24f8_c5ed,
            0x91ba_89b8_d13d_1806,
            0x2f0c_3a11_5d43_17d1,
        ]),
        Fp::from_raw([
            0xd8c5_38a1_dc95_8c61,
            0x08a0_cff6_70b2_2b82,
            0x3006_ed22_0cf9_c810,
            0x0c4e_e778_ff7c_1455,
        ]),
    ],
    [
        Fp::from_raw([
            0x27c3_d748_5de7_4c69,
            0x9424_ed26_c0ac_c662,
            0x3693_f004_40cc_c360,
            0x1704_f276_6d46_f82c,
        ]),
        Fp::from_raw([
            0x39b6_6fe9_009c_3cfa,
            0xf076_9c9f_8544_e402,
            0xa7a0_2c1b_51d2_44ab,
            0x2f2d_19cc_3ea5_d78e,
        ]),
    ],
    [
        Fp::from_raw([
            0xd6c7_66a8_06fc_6629,
            0xdd7e_e6cb_9cfe_d9c7,
            0x5053_f112_e2a8_e8dc,
            0x1ae0_3853_b75f_caba,
        ]),
        Fp::from_raw([
            0x4e41_a86d_daf0_56d5,
            0x3556_921b_2d6f_014e,
            0x51d1_31d0_fa61_aa5f,
            0x0971_aabf_7952_41df,
        ]),
    ],
    [
        Fp::from_raw([
            0x5f5c_29f7_bfe2_f646,
            0xda62_4f83_80df_1c87,
            0x91d4_cf6b_6e0d_e73e,
            0x1408_c316_e601_4e1a,
        ]),
        Fp::from_raw([
            0x4169_1f39_822e_f5bd,
            0x6c89_f1f7_73ef_2853,
            0x248a_be42_b543_093b,
            0x1667_f3fe_2edb_e850,
        ]),
    ],
    [
        Fp::from_raw([
            0x424c_6957_6500_fe37,
            0x5b81_7184_09e5_c133,
            0xa48b_0a03_557c_df91,
            0x13bf_7c5d_0d2c_4376,
        ]),
        Fp::from_raw([
            0x19bc_0ba7_43a6_2c2c,
            0x024b_9534_7856_b797,
            0x3016_adf3_d353_3c24,
            0x0762_0a6d_fb0b_6cec,
        ]),
    ],
    [
        Fp::from_raw([
            0x1675_de3e_1982_b4d0,
            0x75d2_959e_2f32_2b73,
            0x36a8_ca08_bdbd_d8b0,
            0x1574_c7ef_0c43_545f,
        ]),
        Fp::from_raw([
            0xc06e_03a7_ff83_78f0,
            0x5bd4_1845_71c2_54fd,
            0xfd56_7970_a717_ceec,
            0x269e_4b5b_7a2e_b21a,
        ]),
    ],
];
// n: 254
// t: 2
// N: 508
// Result Algorithm 1:
// [True, 0]
// Result Algorithm 2:
// [True, None]
// Result Algorithm 3:
// [True, None]
// Prime number: 0x0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
// MDS matrix:
pub(crate) const MDS: [[Fp; 2]; 2] = [
    [
        Fp::from_raw([
            0xbcec_a70b_d2af_7ad5,
            0xaf07_f38a_f8c9_52a7,
            0xec10_3453_51a2_3a3a,
            0x066f_6f85_d6f6_8a85,
        ]),
        Fp::from_raw([
            0x0546_2b9f_8125_b1e8,
            0x20a7_c02b_bd8b_ea73,
            0x7782_e150_9b1d_0fdb,
            0x2b9d_4b41_10c9_ae99,
        ]),
    ],
    [
        Fp::from_raw([
            0xf573_f431_221f_8ff9,
            0xb6c0_9d55_7013_fff1,
            0x2bf6_7a44_93cc_262f,
            0x0cc5_7cdb_b085_07d6,
        ]),
        Fp::from_raw([
            0x21bc_d147_9432_03c8,
            0xade8_57e8_6eb5_c3a1,
            0xa31a_6ed6_9724_e1ad,
            0x1274_e649_a32e_d355,
        ]),
    ],
];
// Inverse MDS matrix:
pub(crate) const MDS_INV: [[Fp; 2]; 2] = [
    [
        Fp::from_raw([
            0x8dbe_bd0f_a8c5_3e66,
            0x0554_569d_9b29_d1ea,
            0x7081_9ab1_c784_6f21,
            0x13ab_ec39_0ada_7f43,
        ]),
        Fp::from_raw([
            0xaaf6_185b_1a1e_60fe,
            0xbd52_1ead_5dfe_0345,
            0x4c98_62a1_d97d_1510,
            0x1eb9_e1dc_19a3_3a62,
        ]),
    ],
    [
        Fp::from_raw([
            0x763f_7875_036b_cb02,
            0x8ce5_1690_30a2_ad69,
            0x601a_bc49_fdad_4f03,
            0x0fc1_c939_4db8_9bb2,
        ]),
        Fp::from_raw([
            0x8abc_ed6b_d147_c8be,
            0x2b7e_ac34_3459_61bc,
            0x9502_054e_dc03_e7b2,
            0x16a9_e98c_493a_902b,
        ]),
    ],
];