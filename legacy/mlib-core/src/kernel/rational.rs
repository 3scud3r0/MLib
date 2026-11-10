//! Exact rational scalars, with canonical sign and gcd normalization.
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero, Signed};
use std::fmt;
use crate::kernel::{KernelError, KernelResult};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExactScalar(pub(crate) BigRational);

impl ExactScalar {
    pub fn new(num: BigInt, den: BigInt) -> KernelResult<Self> {
        if den.is_zero() { return Err(KernelError::DivisionByZero); }
        Ok(Self(BigRational::new(num, den)))
    }
    pub fn from_i64(n: i64) -> Self { Self(BigRational::from_integer(n.into())) }
    pub fn parse(num: &str, den: &str) -> KernelResult<Self> {
        if num.len() > 16_384 || den.len() > 16_384 {
            return Err(KernelError::ResourceLimit("inteiro excede 16 KiB de dígitos".into()));
        }
        let a = num.parse::<BigInt>().map_err(|_| KernelError::TypeError("numerador inválido".into()))?;
        let b = den.parse::<BigInt>().map_err(|_| KernelError::TypeError("denominador inválido".into()))?;
        Self::new(a, b)
    }
    pub fn zero() -> Self { Self(BigRational::zero()) }
    pub fn one() -> Self { Self(BigRational::one()) }
    pub fn is_zero(&self) -> bool { self.0.is_zero() }
    pub fn is_positive(&self) -> bool { self.0.is_positive() }
    pub fn numer(&self) -> &BigInt { self.0.numer() }
    pub fn den(&self) -> &BigInt { self.0.denom() }
    pub fn negate(&self) -> Self { Self(-self.0.clone()) }
    pub fn add(&self, other: &Self) -> Self { Self(&self.0 + &other.0) }
    pub fn sub(&self, other: &Self) -> Self { Self(&self.0 - &other.0) }
    pub fn mul(&self, other: &Self) -> Self { Self(&self.0 * &other.0) }
    pub fn div(&self, other: &Self) -> KernelResult<Self> {
        if other.is_zero() { return Err(KernelError::DivisionByZero); }
        Ok(Self(&self.0 / &other.0))
    }
    pub fn abs(&self) -> Self { Self(self.0.abs()) }
}
impl fmt::Display for ExactScalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den() == &BigInt::one() { write!(f, "{}", self.numer()) }
        else { write!(f, "{}/{}", self.numer(), self.den()) }
    }
}
impl From<i64> for ExactScalar { fn from(v: i64) -> Self { Self::from_i64(v) } }
