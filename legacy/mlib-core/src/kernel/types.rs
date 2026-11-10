//! Explicit, size-checked geometric types and Lie-algebra structure tensors.
use crate::kernel::{KernelError,KernelResult};
use crate::kernel::rational::ExactScalar as S;

#[derive(Clone,Debug,PartialEq,Eq)]
pub enum MathematicalType {
    RationalVectorSpace{dim:usize},
    InnerProductSpace{dim:usize},
    DualSpace{primal_dim:usize},
    SymplecticPhaseSpace{pairs:usize},
    ContactPhaseSpace{pairs:usize},
    LieAlgebra{dim:usize},
    ProbabilitySimplex{dim:usize},
    FisherRaoManifold{dim:usize},
    IsLocallySymplecticMap{pairs:usize},
    IsNoetherInvariant{pairs:usize},
    IsCasimir{dim:usize},
    IsGcdPolynomial{vars:usize},
    IsValidLieAlgebra{dim:usize},
    IsPositiveDefinite{dim:usize},
}
#[derive(Clone,Debug)]
pub struct LieAlgebra {
    dim:usize,
    constants:Vec<S>,
}
impl LieAlgebra{
    pub fn new(dim:usize,constants:Vec<S>)->KernelResult<Self>{
        if dim==0||dim>128||dim.checked_mul(dim).and_then(|x|x.checked_mul(dim))!=Some(constants.len()){
            return Err(KernelError::DimensionMismatch("tensor de estrutura C[i,j,k]".into()));
        }
        Ok(Self{dim,constants})
    }
    pub fn dim(&self)->usize{self.dim}
    pub fn c(&self,i:usize,j:usize,k:usize)->&S{&self.constants[(i*self.dim+j)*self.dim+k]}
    pub fn check_jacobi(&self)->KernelResult<()> {
        let n=self.dim;
        for i in 0..n{for j in 0..n{for k in 0..n{
            if self.c(i,j,k)!=&self.c(j,i,k).negate(){
                return Err(KernelError::InvalidCertificate(format!("antissimetria {i},{j},{k}")));
            }
        }}}
        for i in 0..n{for j in 0..n{for k in 0..n{for l in 0..n{
            let mut acc=S::zero();
            for m in 0..n{
                acc=acc.add(&self.c(i,j,m).mul(self.c(m,k,l)));
                acc=acc.add(&self.c(j,k,m).mul(self.c(m,i,l)));
                acc=acc.add(&self.c(k,i,m).mul(self.c(m,j,l)));
            }
            if !acc.is_zero(){return Err(KernelError::NonZeroResidual(format!("Jacobi({i},{j},{k},{l})={acc}")));}
        }}}}
        Ok(())
    }
    pub fn constants(&self)->&[S]{&self.constants}
}
