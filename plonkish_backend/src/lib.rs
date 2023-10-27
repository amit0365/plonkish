#![allow(clippy::op_ref)]
#![feature(anonymous_lifetime_in_impl_trait)]
#![feature(associated_type_defaults)]

pub mod accumulation;
pub mod backend;
pub mod frontend;
pub mod pcs;
pub mod piop;
pub mod poly;
pub mod util;

pub use halo2_base::halo2_proofs::halo2curves;

#[derive(Clone, Debug, PartialEq)]
pub enum Error {
    InvalidSumcheck(String),
    InvalidPcsParam(String),
    InvalidPcsOpen(String),
    InvalidSnark(String),
    Serialization(String),
    Transcript(std::io::ErrorKind, String),
}
