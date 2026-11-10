//! Only this module may construct verified theorems.
use crate::kernel::{KernelError,KernelResult};
use crate::kernel::term::{TermArena,TermId};
use crate::kernel::rational::ExactScalar as S;
use crate::kernel::ring::{Polynomial,RationalFunction as RF};
use crate::kernel::types::{LieAlgebra,MathematicalType};
use crate::kernel::canonical::{Normalizer,NormalizedValue};
use crate::kernel::{judgments,linear_algebra};
use std::collections::BTreeSet;

#[derive(Clone,Debug,Default)]
pub struct Environment{lie_algebras:Vec<LieAlgebra>}
impl Environment{
    pub fn new()->Self{Self::default()}
    /// Return a new immutable context. Every registered algebra has had its
    /// full antisymmetry and four-index Jacobi conditions checked.
    pub fn with_lie_algebra(&self,algebra:LieAlgebra)->KernelResult<(Self,usize)>{
        algebra.check_jacobi()?;
        let mut copy=self.clone();let id=copy.lie_algebras.len();
        copy.lie_algebras.push(algebra);Ok((copy,id))
    }
    pub fn lie_algebras(&self)->&[LieAlgebra]{&self.lie_algebras}
}

#[derive(Clone,Debug)]
pub struct CertifiedTheorem {
    id:u64,
    claim:MathematicalType,
    evidence_digest:[u8;32],
    domain:Vec<Polynomial>,
    lean_obligation:Option<String>,
}
impl CertifiedTheorem{
    pub fn id(&self)->u64{self.id}
    pub fn claim(&self)->&MathematicalType{&self.claim}
    pub fn evidence_digest(&self)->&[u8;32]{&self.evidence_digest}
    pub fn digest_hex(&self)->String{hex::encode(self.evidence_digest)}
    pub fn domain_exclusions(&self)->&[Polynomial]{&self.domain}
    /// Export an arithmetic lemma only. The Lean code doesn't automatically
    /// establish an entire flow theorem or certify Rust/Python correctness.
    pub fn to_lean4_code(&self)->Option<&str>{self.lean_obligation.as_deref()}
}

pub struct TypeChecker<'env>{
    env:&'env Environment,
    arena:&'env TermArena,
}
impl<'env> TypeChecker<'env>{
    pub fn new(env:&'env Environment,arena:&'env TermArena)->Self{Self{env,arena}}
    pub fn normalize(&self,id:TermId,nvars:usize)->KernelResult<NormalizedValue>{
        Normalizer::new(self.arena,nvars,self.env.lie_algebras())?.normalize(id)
    }
    pub fn normalize_scalar(&self,id:TermId,nvars:usize)->KernelResult<RF>{
        self.normalize(id,nvars)?.scalar()
    }
    pub fn verify_conservation(&self,pairs:usize,hamiltonian:TermId,observable:TermId)->KernelResult<CertifiedTheorem>{
        let n=pairs.checked_mul(2).ok_or_else(||KernelError::ResourceLimit("dimensão".into()))?;
        if pairs==0||n>128{return Err(KernelError::DimensionMismatch("espaço simplético".into()));}
        let h=self.normalize_scalar(hamiltonian,n)?;
        let q=self.normalize_scalar(observable,n)?;
        let residue=judgments::conservation(&h,&q,pairs)?;
        if !residue.is_zero(){return Err(KernelError::NonZeroResidual(format!("{{Q,H}} = {residue}")));}
        let domains=collect_domains(&[&h,&q,&residue]);
        let evidence=hash_evidence("conservation",n,&[&h,&q],&domains);
        let lean=lean_poisson_obligation(&h,&q,pairs,&evidence)?;
        Ok(make_theorem(MathematicalType::IsNoetherInvariant{pairs},evidence,domains,lean))
    }
    pub fn verify_symplectic_map(&self,pairs:usize,map_terms:&[TermId])->KernelResult<CertifiedTheorem>{
        let n=pairs.checked_mul(2).ok_or_else(||KernelError::ResourceLimit("dimensão".into()))?;
        if pairs==0||n>128||map_terms.len()!=n{return Err(KernelError::DimensionMismatch("mapa 2n -> 2n".into()));}
        let map=map_terms.iter().map(|id|self.normalize_scalar(*id,n)).collect::<KernelResult<Vec<_>>>()?;
        let residual=judgments::symplectic_residual(&map,pairs)?;
        for (i,row) in residual.iter().enumerate(){for (j,entry) in row.iter().enumerate(){
            if !entry.is_zero(){return Err(KernelError::NonZeroResidual(format!("(DΦᵀJDΦ-J)[{i},{j}]={entry}")));}
        }}
        let refs=map.iter().collect::<Vec<_>>();
        let mut all=refs.clone();
        for row in &residual{for x in row{all.push(x);}}
        let domains=collect_domains(&all);
        let evidence=hash_evidence("local_symplectic_map",n,&refs,&domains);
        Ok(make_theorem(MathematicalType::IsLocallySymplecticMap{pairs},evidence,domains,None))
    }
    /// Certify that an untrusted polynomial GCD hint is greatest, not merely
    /// a common divisor: the two exact cofactors must have GCD equal to 1.
    /// The hint is not trusted; every step is recomputed by this kernel.
    pub fn verify_gcd_hint(&self,nvars:usize,a:TermId,b:TermId,hint:TermId)->KernelResult<CertifiedTheorem>{
        if nvars==0||nvars>128{
            return Err(KernelError::DimensionMismatch("GCD exige 1..128 variáveis".into()));
        }
        let aa=self.normalize_scalar(a,nvars)?;
        let bb=self.normalize_scalar(b,nvars)?;
        let gg=self.normalize_scalar(hint,nvars)?;
        for f in [&aa,&bb,&gg]{
            if !f.denominator().is_one()||!f.exclusions().is_empty(){
                return Err(KernelError::DomainSingularity("certificado de GCD requer polinômios globais, não funções racionais com polos".into()));
            }
        }
        if gg.numerator().is_zero(){return Err(KernelError::InvalidCertificate("candidato a GCD igual a zero".into()));}
        if aa.numerator().is_zero() && bb.numerator().is_zero(){
            return Err(KernelError::InvalidCertificate("GCD(0,0) indeterminado".into()));
        }
        let divisor=gg.numerator().monic();
        let co_a=aa.numerator().exact_div(&divisor).map_err(|_|KernelError::InvalidCertificate("candidato não divide A".into()))?;
        let co_b=bb.numerator().exact_div(&divisor).map_err(|_|KernelError::InvalidCertificate("candidato não divide B".into()))?;
        if !co_a.gcd(&co_b)?.is_one(){
            return Err(KernelError::InvalidCertificate("cofatores possuem divisor comum não constante".into()));
        }
        let evidence=hash_evidence("gcd_polynomial",nvars,&[&aa,&bb,&gg],&[]);
        Ok(make_theorem(MathematicalType::IsGcdPolynomial{vars:nvars},evidence,Vec::new(),None))
    }
    pub fn verify_lie_algebra(&self,algebra:&LieAlgebra)->KernelResult<CertifiedTheorem>{
        algebra.check_jacobi()?;
        let mut h=blake3::Hasher::new();h.update(b"mlib-kernel-v1:lie_algebra");
        feed_usize(&mut h,algebra.dim());
        for scalar in algebra.constants(){feed_scalar(&mut h,scalar);}
        let bytes=*h.finalize().as_bytes();
        Ok(make_theorem(MathematicalType::IsValidLieAlgebra{dim:algebra.dim()},bytes,Vec::new(),None))
    }
    pub fn verify_positive_gram(&self,gram:&[Vec<S>])->KernelResult<CertifiedTheorem>{
        linear_algebra::positive_definite_ldlt(gram)?;
        let mut h=blake3::Hasher::new();h.update(b"mlib-kernel-v1:positive_gram");
        feed_usize(&mut h,gram.len());
        for row in gram{for x in row{feed_scalar(&mut h,x);}}
        Ok(make_theorem(MathematicalType::IsPositiveDefinite{dim:gram.len()},*h.finalize().as_bytes(),Vec::new(),None))
    }
    pub fn verify_casimir(&self,algebra:&LieAlgebra,term:TermId)->KernelResult<CertifiedTheorem>{
        algebra.check_jacobi()?;
        let c=self.normalize_scalar(term,algebra.dim())?;
        for (j,residual) in judgments::casimir_residual(&c,algebra)?.iter().enumerate(){
            if !residual.is_zero(){return Err(KernelError::NonZeroResidual(format!("Casimir {j}: {residual}")));}
        }
        let domains=collect_domains(&[&c]);
        let mut h=blake3::Hasher::new();h.update(b"mlib-kernel-v1:casimir");
        feed_usize(&mut h,algebra.dim());
        for x in algebra.constants(){feed_scalar(&mut h,x);}
        feed_rational(&mut h,&c);
        for p in &domains{feed_poly(&mut h,p);}
        Ok(make_theorem(MathematicalType::IsCasimir{dim:algebra.dim()},*h.finalize().as_bytes(),domains,None))
    }
}
fn make_theorem(claim:MathematicalType,evidence_digest:[u8;32],domain:Vec<Polynomial>,lean_obligation:Option<String>)->CertifiedTheorem{
    let id=u64::from_le_bytes(evidence_digest[..8].try_into().expect("32 byte digest"));
    CertifiedTheorem{id,claim,evidence_digest,domain,lean_obligation}
}
fn collect_domains(entries:&[&RF])->Vec<Polynomial>{
    entries.iter().flat_map(|x|x.exclusions().iter().cloned()).collect::<BTreeSet<_>>().into_iter().collect()
}
fn feed_usize(hasher:&mut blake3::Hasher,n:usize){hasher.update(&(n as u64).to_le_bytes());}
fn feed_str(h:&mut blake3::Hasher,s:&str){feed_usize(h,s.len());h.update(s.as_bytes());}
fn feed_scalar(h:&mut blake3::Hasher,x:&S){feed_str(h,&x.numer().to_string());feed_str(h,&x.den().to_string());}
fn feed_poly(h:&mut blake3::Hasher,p:&Polynomial){
    feed_usize(h,p.nvars());feed_usize(h,p.terms().len());
    for (exp,c) in p.terms(){for x in exp{h.update(&x.to_le_bytes());}feed_scalar(h,c);}
}
fn feed_rational(h:&mut blake3::Hasher,p:&RF){
    feed_poly(h,p.numerator());feed_poly(h,p.denominator());
    feed_usize(h,p.exclusions().len());for x in p.exclusions(){feed_poly(h,x);}
}
fn hash_evidence(tag:&str,n:usize,values:&[&RF],domain:&[Polynomial])->[u8;32]{
    let mut h=blake3::Hasher::new();h.update(b"mlib-kernel-v1");feed_str(&mut h,tag);
    feed_usize(&mut h,n);feed_usize(&mut h,values.len());
    for p in values{feed_rational(&mut h,p);}
    feed_usize(&mut h,domain.len());for p in domain{feed_poly(&mut h,p);}
    *h.finalize().as_bytes()
}
fn lean_poly(p:&Polynomial)->String{
    if p.is_zero(){return "(0 : ℚ)".to_string();}
    let mut sum=Vec::new();
    for (exp,c) in p.terms(){
        let coefficient=if c.den().to_string()=="1"{format!("({} : ℚ)",c.numer())}
            else{format!("(({} : ℚ) / ({} : ℚ))",c.numer(),c.den())};
        let mut factors=vec![coefficient];
        for (i,k) in exp.iter().enumerate(){if *k==1{factors.push(format!("x{i}"));}
            else if *k>1{factors.push(format!("(x{i} ^ {k})"));}}
        sum.push(format!("({})",factors.join(" * ")));
    }
    format!("({})",sum.join(" + "))
}
fn lean_poisson_obligation(h:&RF,q:&RF,pairs:usize,hash:&[u8;32])->KernelResult<Option<String>>{
    if !h.denominator().is_one()||!q.denominator().is_one()||!h.exclusions().is_empty()||!q.exclusions().is_empty(){return Ok(None);}
    let mut expression=Vec::new();
    let hh=h.numerator();let qq=q.numerator();
    for i in 0..pairs{
        expression.push(format!("({} * {} - {} * {})",lean_poly(&qq.diff(i)?),lean_poly(&hh.diff(pairs+i)?),lean_poly(&qq.diff(pairs+i)?),lean_poly(&hh.diff(i)?)));
    }
    let vars=(0..pairs*2).map(|i|format!("x{i}")).collect::<Vec<_>>().join(" ");
    let name=format!("mlib_poisson_{}",hex::encode(&hash[..6]));
    Ok(Some(format!("import Mathlib\n\n-- Machine-generated arithmetic obligation; NOT a general flow theorem.\ntheorem {name} ({vars} : ℚ) :\n  ({}) = (0 : ℚ) := by\n  ring\n",expression.join(" + "))))
}
