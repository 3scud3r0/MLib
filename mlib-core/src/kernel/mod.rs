#![forbid(unsafe_code)]

pub mod rational;
pub mod term;
pub mod ring;
pub mod canonical;
pub mod linear_algebra;
pub mod types;
pub mod judgments;
pub mod type_checker;

use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum KernelError {
    #[error("divisão por zero ou denominador polinomial identicamente nulo")]
    DivisionByZero,
    #[error("dimensões incompatíveis: {0}")]
    DimensionMismatch(String),
    #[error("índice de termo ou variável inválido: {0}")]
    InvalidIndex(usize),
    #[error("expressão ou operação mal tipada: {0}")]
    TypeError(String),
    #[error("violação de domínio: {0}")]
    DomainSingularity(String),
    #[error("recurso excedido: {0}")]
    ResourceLimit(String),
    #[error("identidade não provada; resíduo exato: {0}")]
    NonZeroResidual(String),
    #[error("certificado estrutural inválido: {0}")]
    InvalidCertificate(String),
    #[error("não foi possível dividir exatamente um polinômio pelo outro")]
    NonExactDivision,
    #[error("função não implementada neste domínio matemático: {0}")]
    Unsupported(String),
}

pub type KernelResult<T> = Result<T, KernelError>;
