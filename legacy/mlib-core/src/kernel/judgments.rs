//! Mathematical inference rules supported by the trusted checker.
//!
//! * `{Q,H} = 0` (on all points of the disclosed rational domain) certifies
//!   continuous-time conservation for trajectories staying in that domain.
//! * `DΦᵀ J DΦ = J` certifies **local** symplecticity on that domain.
//!   Global bijectivity is deliberately not claimed.
//! * Antisymmetry + every indexed Jacobi equation certify Lie structure constants.
//! * Symmetry + positive exact LDLᵀ pivots certify strict Gram positivity.
//!
//! These are exact decision procedures for restricted first-order identities,
//! not a dependent-type proof assistant nor a general formalization of Lean.
use crate::kernel::{KernelError,KernelResult};
use crate::kernel::ring::{Polynomial,RationalFunction as RF};
use crate::kernel::canonical::poisson;
use crate::kernel::types::LieAlgebra;

pub fn conservation(hamiltonian:&RF,observable:&RF,pairs:usize)->KernelResult<RF>{
    poisson(observable,hamiltonian,pairs)
}
pub fn symplectic_residual(map:&[RF],pairs:usize)->KernelResult<Vec<Vec<RF>>>{
    let n=pairs.checked_mul(2).ok_or_else(||KernelError::ResourceLimit("dimensão".into()))?;
    if pairs==0 || map.len()!=n || map.iter().any(|f|f.nvars()!=n){
        return Err(KernelError::DimensionMismatch("mapa simplético deve ser 2n -> 2n".into()));
    }
    let mut d=Vec::with_capacity(n);
    for f in map{d.push((0..n).map(|i|f.diff(i)).collect::<KernelResult<Vec<_>>>()?);}
    let mut out=vec![vec![RF::zero(n);n];n];
    // J = [[0,I],[-I,0]], so (Dᵀ J D)ij = sum_k (dQk/di*dPk/dj - dPk/di*dQk/dj).
    for i in 0..n{for j in 0..n{
        let mut x=RF::zero(n);
        for k in 0..pairs{
            x=x.add(&d[k][i].mul(&d[pairs+k][j])?)?;
            x=x.sub(&d[pairs+k][i].mul(&d[k][j])?)?;
        }
        let jij=if i<pairs&&j==pairs+i{1}else if i>=pairs&&j==i-pairs{-1}else{0};
        out[i][j]=x.sub(&RF::from_poly(Polynomial::constant(n,jij.into())))?;
    }}
    Ok(out)
}
pub fn casimir_residual(candidate:&RF,algebra:&LieAlgebra)->KernelResult<Vec<RF>>{
    let n=algebra.dim();
    if candidate.nvars()!=n{return Err(KernelError::DimensionMismatch("Casimir de Lie-Poisson".into()));}
    let mut out=Vec::with_capacity(n);
    for j in 0..n{
        let mut residual=RF::zero(n);
        for i in 0..n{for k in 0..n{
            let coeff=algebra.c(i,j,k);
            if coeff.is_zero(){continue;}
            let factor=RF::from_poly(Polynomial::var(n,k)?.scale(coeff));
            residual=residual.add(&candidate.diff(i)?.mul(&factor)?)?;
        }}
        out.push(residual);
    }
    Ok(out)
}
