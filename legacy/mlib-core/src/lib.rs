//! Exact Rust checker for a restricted, explicitly scoped mathematical logic.
//!
//! The Python/GPU proposer is untrusted. Only constructors in this crate's
//! `kernel::type_checker` can produce a `CertifiedTheorem`.
//!
//! A BLAKE3 digest is an *integrity fingerprint*, not a digital signature and
//! not a replacement for independent replay of a proof certificate.
//!
//! ```compile_fail
//! use mlib_core::kernel::type_checker::CertifiedTheorem;
//! // The theorem constructor is intentionally private to the checking kernel.
//! let forged = CertifiedTheorem { id: 1, claim: panic!(), evidence_digest: [0;32], domain: vec![], lean_obligation: None };
//! ```

pub mod kernel;
#[cfg(feature = "python")]
pub mod ffi;

pub use kernel::rational::ExactScalar;
pub use kernel::ring::{Polynomial, RationalFunction};
pub use kernel::term::{TermArena, TermId, TermNode};
pub use kernel::type_checker::{CertifiedTheorem, Environment, TypeChecker};
pub use kernel::types::{LieAlgebra, MathematicalType};
