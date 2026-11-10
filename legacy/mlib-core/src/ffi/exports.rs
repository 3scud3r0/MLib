//! Python extension; all certificates originate from the Rust checker.
use crate::ffi::conversions::{into_arena,parse_json};
use crate::kernel::rational::ExactScalar as S;
use crate::kernel::term::TermArena;
use crate::kernel::type_checker::{CertifiedTheorem,Environment,TypeChecker};
use crate::kernel::types::LieAlgebra;
use pyo3::prelude::*;
use pyo3::exceptions::PyValueError;

fn pyerr(e:impl std::fmt::Display)->PyErr{PyValueError::new_err(e.to_string())}

#[pyclass(frozen, module="mlib_core")]
pub struct PyCertifiedTheorem{inner:CertifiedTheorem}
#[pymethods]
impl PyCertifiedTheorem{
    #[getter]
    fn digest(&self)->String{self.inner.digest_hex()}
    #[getter]
    fn claim(&self)->String{format!("{:?}",self.inner.claim())}
    #[getter]
    fn original_domain_exclusions(&self)->Vec<String>{self.inner.domain_exclusions().iter().map(ToString::to_string).collect()}
    fn to_lean4_code(&self)->Option<String>{self.inner.to_lean4_code().map(str::to_owned)}
    fn __repr__(&self)->String{format!("CertifiedTheorem(claim={}, digest={})",self.claim(),self.digest())}
}

#[pyclass(module="mlib_core")]
pub struct MlibKernelContext{env:Environment}
#[pymethods]
impl MlibKernelContext{
    #[new]
    fn new()->Self{Self{env:Environment::new()}}
    /// JSON example: {"op":"mul","left":{"op":"var","index":0},"right":{"op":"var","index":1}}
    fn verify_noether(&mut self,pairs:usize,hamiltonian_json:&str,candidate_json:&str)->PyResult<PyCertifiedTheorem>{
        // Each proposal has a fresh, resource-limited arena: invalid model
        // outputs cannot gradually exhaust a persistent arena across calls.
        let mut arena=TermArena::new(100_000);
        let h=into_arena(&parse_json(hamiltonian_json).map_err(pyerr)?,&mut arena,0).map_err(pyerr)?;
        let q=into_arena(&parse_json(candidate_json).map_err(pyerr)?,&mut arena,0).map_err(pyerr)?;
        let checked=TypeChecker::new(&self.env,&arena).verify_conservation(pairs,h,q).map_err(pyerr)?;
        Ok(PyCertifiedTheorem{inner:checked})
    }
    fn verify_gcd_hint(&mut self,nvars:usize,a_json:&str,b_json:&str,hint_json:&str)->PyResult<PyCertifiedTheorem>{
        if nvars==0||nvars>128{return Err(pyerr("GCD exige 1..128 variáveis"));}
        let mut arena=TermArena::new(100_000);
        let a=into_arena(&parse_json(a_json).map_err(pyerr)?,&mut arena,0).map_err(pyerr)?;
        let b=into_arena(&parse_json(b_json).map_err(pyerr)?,&mut arena,0).map_err(pyerr)?;
        let hint=into_arena(&parse_json(hint_json).map_err(pyerr)?,&mut arena,0).map_err(pyerr)?;
        let checked=TypeChecker::new(&self.env,&arena).verify_gcd_hint(nvars,a,b,hint).map_err(pyerr)?;
        Ok(PyCertifiedTheorem{inner:checked})
    }
    fn verify_symplectic(&mut self,pairs:usize,map_json:&str)->PyResult<PyCertifiedTheorem>{
        if map_json.len()>2_000_000{return Err(pyerr("mapa JSON > 2 MB"));}
        let maps:Vec<serde_json::Value>=serde_json::from_str(map_json).map_err(pyerr)?;
        if maps.len()!=pairs.saturating_mul(2)||pairs==0||pairs>64{return Err(pyerr("mapa deve ter 2*pairs coordenadas"));}
        let mut arena=TermArena::new(100_000);
        let mut terms=Vec::with_capacity(maps.len());
        for element in maps{
            let ast=serde_json::from_value(element).map_err(pyerr)?;
            terms.push(into_arena(&ast,&mut arena,0).map_err(pyerr)?);
        }
        let checked=TypeChecker::new(&self.env,&arena).verify_symplectic_map(pairs,&terms).map_err(pyerr)?;
        Ok(PyCertifiedTheorem{inner:checked})
    }
    fn verify_positive_gram(&self,gram:Vec<Vec<String>>)->PyResult<PyCertifiedTheorem>{
        let matrix=gram.iter().map(|row|row.iter().map(|v|{
            let parts=v.split('/').collect::<Vec<_>>();
            match parts.as_slice(){[a]=>S::parse(a,"1"),[a,b]=>S::parse(a,b),_=>Err(crate::kernel::KernelError::TypeError("racional inválido".into()))}
        }).collect::<crate::kernel::KernelResult<Vec<_>>>()).collect::<crate::kernel::KernelResult<Vec<_>>>().map_err(pyerr)?;
        let arena=TermArena::new(1);
        let checked=TypeChecker::new(&self.env,&arena).verify_positive_gram(&matrix).map_err(pyerr)?;
        Ok(PyCertifiedTheorem{inner:checked})
    }
    fn verify_lie(&self,dim:usize,constants:Vec<String>)->PyResult<PyCertifiedTheorem>{
        let values=constants.iter().map(|v|{
            let parts=v.split('/').collect::<Vec<_>>();
            match parts.as_slice(){[a]=>S::parse(a,"1"),[a,b]=>S::parse(a,b),_=>Err(crate::kernel::KernelError::TypeError("coeficiente inválido".into()))}
        }).collect::<crate::kernel::KernelResult<Vec<_>>>().map_err(pyerr)?;
        let algebra=LieAlgebra::new(dim,values).map_err(pyerr)?;
        let arena=TermArena::new(1);
        let checked=TypeChecker::new(&self.env,&arena).verify_lie_algebra(&algebra).map_err(pyerr)?;
        Ok(PyCertifiedTheorem{inner:checked})
    }
}

#[pymodule]
pub fn _mlib_core(m:&Bound<'_,PyModule>)->PyResult<()>{
    m.add_class::<MlibKernelContext>()?;
    m.add_class::<PyCertifiedTheorem>()?;
    Ok(())
}
