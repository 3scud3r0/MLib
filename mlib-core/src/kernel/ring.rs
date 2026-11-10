//! Exact Q[x_0,...,x_{n-1}] and its field of fractions.
//!
//! Monomials are stored in a deterministic ordered map.  Polynomial GCD uses
//! recursive Euclid over Q(x_0,...,x_{n-2})[x_{n-1}], followed by Gauss-lemma
//! primitive-part extraction, not a probabilistic factor heuristic.
//!
//! Domain exclusions are *never dropped* when factors are canceled. Thus
//! (x/x) and 1 have the same algebraic value but different original domains.
use crate::kernel::{KernelError, KernelResult};
use crate::kernel::rational::ExactScalar as S;
use num_traits::One;
use std::collections::{BTreeMap, BTreeSet};
use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Polynomial {
    nvars: usize,
    terms: BTreeMap<Vec<u32>, S>,
}

fn cmp_grevlex(a: &[u32], b: &[u32]) -> Ordering {
    let da: u64 = a.iter().map(|x| u64::from(*x)).sum();
    let db: u64 = b.iter().map(|x| u64::from(*x)).sum();
    da.cmp(&db).then_with(|| {
        for (x,y) in a.iter().zip(b).rev() {
            if x != y { return y.cmp(x); }
        }
        Ordering::Equal
    })
}
fn divides(a: &[u32], b: &[u32]) -> bool {
    a.iter().zip(b).all(|(i,j)| i <= j)
}

impl Polynomial {
    pub fn zero(nvars: usize) -> Self { Self { nvars, terms: BTreeMap::new() } }
    pub fn one(nvars: usize) -> Self { Self::constant(nvars, S::one()) }
    pub fn constant(nvars: usize, c: S) -> Self {
        let mut p=Self::zero(nvars);
        if !c.is_zero() { p.terms.insert(vec![0;nvars],c); }
        p
    }
    pub fn var(nvars: usize, index: usize) -> KernelResult<Self> {
        if index >= nvars { return Err(KernelError::InvalidIndex(index)); }
        let mut e=vec![0;nvars];e[index]=1;
        Self::from_terms(nvars,[(e,S::one())])
    }
    pub fn from_terms<I>(nvars:usize, terms:I) -> KernelResult<Self>
    where I: IntoIterator<Item=(Vec<u32>,S)> {
        let mut out=Self::zero(nvars);
        for (exp,c) in terms {
            if exp.len()!=nvars { return Err(KernelError::DimensionMismatch("expoente monomial".into())); }
            if c.is_zero() {continue;}
            let prev=out.terms.remove(&exp).unwrap_or_else(S::zero);
            let next=prev.add(&c);
            if !next.is_zero() {out.terms.insert(exp,next);}
        }
        Ok(out)
    }
    pub fn nvars(&self) -> usize {self.nvars}
    pub fn terms(&self) -> &BTreeMap<Vec<u32>,S> {&self.terms}
    pub fn is_zero(&self) -> bool {self.terms.is_empty()}
    pub fn is_one(&self) -> bool {self==&Self::one(self.nvars)}
    pub fn is_constant(&self) -> bool {self.terms.keys().all(|a|a.iter().all(|x|*x==0))}
    pub fn is_nonzero_constant(&self) -> bool {self.is_constant() && !self.is_zero()}
    pub fn lead(&self) -> Option<(&Vec<u32>,&S)> {
        self.terms.iter().max_by(|(a,_),(b,_)|cmp_grevlex(a,b))
    }
    pub fn degree(&self) -> u64 {
        self.terms.keys().map(|e|e.iter().map(|x|u64::from(*x)).sum()).max().unwrap_or(0)
    }
    fn same(&self,b:&Self)->KernelResult<()> {
        if self.nvars!=b.nvars {return Err(KernelError::DimensionMismatch("anéis polinomiais diferentes".into()));}
        Ok(())
    }
    pub fn add(&self,b:&Self)->KernelResult<Self>{
        self.same(b)?;
        let mut out=self.clone();
        for (e,c) in &b.terms {
            let val=out.terms.remove(e).unwrap_or_else(S::zero).add(c);
            if !val.is_zero() {out.terms.insert(e.clone(),val);}
        }
        Ok(out)
    }
    pub fn neg(&self)->Self{ Self{nvars:self.nvars,terms:self.terms.iter().map(|(e,c)|(e.clone(),c.negate())).collect()} }
    pub fn sub(&self,b:&Self)->KernelResult<Self>{self.add(&b.neg())}
    pub fn scale(&self,c:&S)->Self{
        if c.is_zero(){return Self::zero(self.nvars)}
        Self{nvars:self.nvars,terms:self.terms.iter().map(|(e,v)|(e.clone(),v.mul(c))).collect()}
    }
    pub fn mul(&self,b:&Self)->KernelResult<Self>{
        self.same(b)?;
        let mut out=Self::zero(self.nvars);
        for (a,ca) in &self.terms { for (e,ce) in &b.terms {
            let degrees=a.iter().zip(e).map(|(x,y)| x.checked_add(*y).ok_or_else(||KernelError::ResourceLimit("expoente u32 excedido".into()))).collect::<KernelResult<Vec<_>>>()?;
            let next=out.terms.remove(&degrees).unwrap_or_else(S::zero).add(&ca.mul(ce));
            if !next.is_zero(){out.terms.insert(degrees,next);}
        }}
        Ok(out)
    }
    pub fn pow(&self,k:u32)->KernelResult<Self>{
        let mut acc=Self::one(self.nvars); let mut base=self.clone(); let mut exp=k;
        while exp>0 {if exp&1!=0{acc=acc.mul(&base)?;} exp>>=1; if exp>0 {base=base.mul(&base)?;} }
        Ok(acc)
    }
    pub fn diff(&self,var:usize)->KernelResult<Self>{
        if var>=self.nvars {return Err(KernelError::InvalidIndex(var));}
        let mut out=Self::zero(self.nvars);
        for (a,c) in &self.terms {if a[var]>0 {
            let mut e=a.clone();e[var]-=1;
            out.terms.insert(e,c.mul(&S::new(a[var].into(),1.into())?));
        }}
        Ok(out)
    }
    pub fn monic(&self)->Self {
        match self.lead(){None=>self.clone(),Some((_,c))=>self.scale(&S::one().div(c).expect("nonzero leading coefficient"))}
    }
    pub fn div_rem(&self,den:&Self)->KernelResult<(Self,Self)>{
        self.same(den)?;
        if den.is_zero(){return Err(KernelError::DivisionByZero);}
        let (de,dc)=den.lead().expect("nonzero denominator");
        let mut quotient=Self::zero(self.nvars);let mut remainder=Self::zero(self.nvars);let mut work=self.clone();
        while let Some((we,wc))=work.lead(){
            let e=we.clone();let c=wc.clone();
            if divides(de,&e){
                let x=Self::from_terms(self.nvars,[(e.iter().zip(de).map(|(i,j)|i-j).collect(), c.div(dc)?)])?;
                quotient=quotient.add(&x)?;
                work=work.sub(&den.mul(&x)?)?;
            }else{
                let leading=Self::from_terms(self.nvars,[(e,c)])?;
                remainder=remainder.add(&leading)?;
                work=work.sub(&leading)?;
            }
        }
        Ok((quotient,remainder))
    }
    pub fn exact_div(&self,den:&Self)->KernelResult<Self>{
        let (q,r)=self.div_rem(den)?;
        if !r.is_zero(){return Err(KernelError::NonExactDivision);}
        Ok(q)
    }
    pub fn evaluate(&self,values:&[S])->KernelResult<S>{
        if values.len()!=self.nvars{return Err(KernelError::DimensionMismatch("avaliação".into()));}
        let mut acc=S::zero();
        for (e,c) in &self.terms {
            let mut term=c.clone();
            for (x,k) in values.iter().zip(e){for _ in 0..*k {term=term.mul(x);}}
            acc=acc.add(&term);
        }
        Ok(acc)
    }
    fn split_last(&self)->KernelResult<Vec<Self>>{
        if self.nvars==0 {return Err(KernelError::DimensionMismatch("não existem variáveis".into()));}
        let max=self.terms.keys().map(|e|e[self.nvars-1]).max().unwrap_or(0);
        if max>4096{return Err(KernelError::ResourceLimit("grau de gcd > 4096".into()));}
        let mut out=vec![Self::zero(self.nvars-1);max as usize+1];
        for (e,c) in &self.terms{
            let idx=e[self.nvars-1] as usize;
            let t=Self::from_terms(self.nvars-1,[(e[..self.nvars-1].to_vec(),c.clone())])?;
            out[idx]=out[idx].add(&t)?;
        }
        Ok(out)
    }
    fn join_last(coeffs:&[Self])->KernelResult<Self>{
        let lower=coeffs.first().ok_or_else(||KernelError::TypeError("coeficientes vazios".into()))?.nvars;
        let mut out=Self::zero(lower+1);
        for (k,p) in coeffs.iter().enumerate(){
            if p.nvars!=lower {return Err(KernelError::DimensionMismatch("coeficientes".into()));}
            let deg=u32::try_from(k).map_err(|_|KernelError::ResourceLimit("grau excedido".into()))?;
            for (e,c) in &p.terms{let mut ee=e.clone();ee.push(deg);
                out=out.add(&Self::from_terms(lower+1,[(ee,c.clone())])?)?;
            }
        }
        Ok(out)
    }
    pub fn gcd(&self,other:&Self)->KernelResult<Self>{
        self.same(other)?;
        if self.is_zero(){return Ok(other.monic())}
        if other.is_zero(){return Ok(self.monic())}
        // Safe deterministic fast paths: avoid recursive polynomial-field
        // Euclid for equal inputs, units, or an explicit monomial factor.
        if self==other{return Ok(self.monic());}
        if self.is_nonzero_constant()||other.is_nonzero_constant(){return Ok(Self::one(self.nvars));}
        if self.terms.len()==1 || other.terms.len()==1 {
            let (mono,poly)=if self.terms.len()==1{(self,other)}else{(other,self)};
            let (exponent,_) = mono.lead().expect("nonzero monomial");
            let powers=(0..self.nvars).map(|i|{
                let min_power=poly.terms.keys().map(|p|p[i]).min().unwrap_or(0);
                exponent[i].min(min_power)
            }).collect::<Vec<_>>();
            return Self::from_terms(self.nvars,[(powers,S::one())]);
        }
        if self.nvars==0{return Ok(Self::one(0));}
        let a=self.split_last()?;let b=other.split_last()?;
        let ca=gcd_many(&a)?;let cb=gcd_many(&b)?;
        let primitive_a=a.iter().map(|x|x.exact_div(&ca)).collect::<KernelResult<Vec<_>>>()?;
        let primitive_b=b.iter().map(|x|x.exact_div(&cb)).collect::<KernelResult<Vec<_>>>()?;
        let mut u=primitive_a.into_iter().map(RationalFunction::from_poly).collect::<Vec<_>>();
        let mut v=primitive_b.into_iter().map(RationalFunction::from_poly).collect::<Vec<_>>();
        trim(&mut u);trim(&mut v);
        let gcd_field=univariate_gcd(u,v)?;
        // Clear all coefficient denominators without heuristic factorization.
        let k=gcd_field.len();let lower=self.nvars-1;
        let mut coeffs=Vec::with_capacity(k);
        for (i,rf) in gcd_field.iter().enumerate(){
            let mut c=rf.numer.clone();
            for (j,other_rf) in gcd_field.iter().enumerate(){if i!=j{c=c.mul(&other_rf.denom)?;}}
            coeffs.push(c);
        }
        if coeffs.is_empty(){return Ok(Self::one(self.nvars));}
        let content=gcd_many(&coeffs)?;
        let primitive=coeffs.iter().map(|p|p.exact_div(&content)).collect::<KernelResult<Vec<_>>>()?;
        let content_gcd=ca.gcd(&cb)?;
        let joined=Self::join_last(&primitive)?;
        let lifted=Self::join_last(&[content_gcd])?;
        let result=joined.mul(&lifted)?.monic();
        if result.nvars()!=lower+1 || self.div_rem(&result)?.1.is_zero()==false || other.div_rem(&result)?.1.is_zero()==false {
            return Err(KernelError::InvalidCertificate("gcd recursivo falhou na divisão exata".into()));
        }
        Ok(result)
    }
}
fn gcd_many(p:&[Polynomial])->KernelResult<Polynomial>{
    let zero=p.first().ok_or_else(||KernelError::TypeError("sequência vazia".into()))?.nvars;
    let mut g=Polynomial::zero(zero);
    for x in p {g=g.gcd(x)?;if g.is_one(){break;}}
    Ok(g)
}
fn trim(poly:&mut Vec<RationalFunction>) {
    while poly.last().is_some_and(RationalFunction::is_zero){poly.pop();}
}
fn udiv_rem(a:&[RationalFunction],b:&[RationalFunction])->KernelResult<Vec<RationalFunction>>{
    if b.is_empty(){return Err(KernelError::DivisionByZero);}
    let mut r=a.to_vec();trim(&mut r);
    if r.is_empty(){return Ok(r);}
    let dim=b[0].nvars();
    while r.len()>=b.len() && !r.is_empty(){
        let lead=r.last().expect("nonempty").div(b.last().expect("nonempty"))?;
        let shift=r.len()-b.len();
        for (i,bi) in b.iter().enumerate(){let idx=i+shift;
            r[idx]=r[idx].sub(&lead.mul(bi)?)?;
        }
        trim(&mut r);
        if r.len()>4096 {return Err(KernelError::ResourceLimit("grau de gcd".into()));}
    }
    if r.iter().any(|x|x.nvars()!=dim){return Err(KernelError::DimensionMismatch("coeficientes de gcd".into()));}
    Ok(r)
}
fn univariate_gcd(mut a:Vec<RationalFunction>,mut b:Vec<RationalFunction>)->KernelResult<Vec<RationalFunction>>{
    trim(&mut a);trim(&mut b);
    while !b.is_empty(){let r=udiv_rem(&a,&b)?;a=b;b=r;}
    if a.is_empty(){return Ok(a);}
    let lc=a.last().expect("nonempty").clone();
    a.into_iter().map(|c|c.div(&lc)).collect()
}
impl fmt::Display for Polynomial {
    fn fmt(&self,f:&mut fmt::Formatter<'_>)->fmt::Result {
        if self.is_zero(){return write!(f,"0");}
        let mut terms=self.terms.iter().collect::<Vec<_>>();
        terms.sort_by(|(a,_),(b,_)|cmp_grevlex(b,a));
        for (i,(exp,c)) in terms.iter().enumerate(){
            if i>0{write!(f," + ")?;}
            write!(f,"({c})")?;
            for (j,k) in exp.iter().enumerate(){if *k>0{write!(f,"*x{j}^{k}")?;}}
        }
        Ok(())
    }
}

#[derive(Clone,Debug,PartialEq,Eq,Hash)]
pub struct RationalFunction {
    pub(crate) numer:Polynomial,
    pub(crate) denom:Polynomial,
    /// Original (pre-cancellation) denominators and division-by-numerator guards.
    pub(crate) excluded:BTreeSet<Polynomial>,
}
impl RationalFunction {
    pub fn zero(nvars:usize)->Self{Self::from_poly(Polynomial::zero(nvars))}
    pub fn one(nvars:usize)->Self{Self::from_poly(Polynomial::one(nvars))}
    pub fn from_poly(p:Polynomial)->Self{let den=Polynomial::one(p.nvars());Self{numer:p,denom:den,excluded:BTreeSet::new()}}
    pub fn new(numer:Polynomial,denom:Polynomial)->KernelResult<Self>{Self::with_domain(numer,denom,BTreeSet::new())}
    fn with_domain(numer:Polynomial,denom:Polynomial,mut excluded:BTreeSet<Polynomial>)->KernelResult<Self>{
        numer.same(&denom)?;
        if denom.is_zero(){return Err(KernelError::DivisionByZero);}
        if !denom.is_nonzero_constant(){excluded.insert(denom.monic());}
        let nvars=numer.nvars();
        // A denominator from Q* needs no multivariate GCD. Previously,
        // polynomial-only operations triggered recursive Euclid at each AST
        // node; eliminating that hot path improves high-dimensional cases.
        if numer.is_zero(){
            excluded.retain(|p|!p.is_nonzero_constant());
            return Ok(Self{numer:Polynomial::zero(nvars),denom:Polynomial::one(nvars),excluded});
        }
        if denom.is_nonzero_constant(){
            let scalar=denom.lead().expect("nonzero constant").1;
            let inv=S::one().div(scalar)?;
            excluded.retain(|p|!p.is_nonzero_constant());
            return Ok(Self{numer:numer.scale(&inv),denom:Polynomial::one(nvars),excluded});
        }
        if numer==denom {
            excluded.retain(|p|!p.is_nonzero_constant());
            return Ok(Self{numer:Polynomial::one(nvars),denom:Polynomial::one(nvars),excluded});
        }
        let gcd=numer.gcd(&denom)?;
        let mut a=numer.exact_div(&gcd)?;let mut b=denom.exact_div(&gcd)?;
        let leading=b.lead().expect("denominator nonzero").1.clone();
        let inv=S::one().div(&leading)?;
        a=a.scale(&inv);b=b.scale(&inv);
        if a.is_zero(){a=Polynomial::zero(nvars);b=Polynomial::one(nvars);}
        excluded.retain(|p|!p.is_nonzero_constant());
        Ok(Self{numer:a,denom:b,excluded})
    }
    pub fn nvars(&self)->usize{self.numer.nvars()}
    pub fn numerator(&self)->&Polynomial{&self.numer}
    pub fn denominator(&self)->&Polynomial{&self.denom}
    pub fn exclusions(&self)->&BTreeSet<Polynomial>{&self.excluded}
    pub fn is_zero(&self)->bool{self.numer.is_zero()}
    pub fn is_one(&self)->bool{self.numer==self.denom}
    fn same(&self,b:&Self)->KernelResult<()> {self.numer.same(&b.numer)}
    fn guards(&self,b:&Self)->BTreeSet<Polynomial>{self.excluded.union(&b.excluded).cloned().collect()}
    pub fn add(&self,b:&Self)->KernelResult<Self>{
        self.same(b)?;
        if self.denom==b.denom {
            return Self::with_domain(self.numer.add(&b.numer)?,self.denom.clone(),self.guards(b));
        }
        Self::with_domain(self.numer.mul(&b.denom)?.add(&b.numer.mul(&self.denom)?)?,self.denom.mul(&b.denom)?,self.guards(b))
    }
    pub fn neg(&self)->Self{Self{numer:self.numer.neg(),denom:self.denom.clone(),excluded:self.excluded.clone()}}
    pub fn sub(&self,b:&Self)->KernelResult<Self>{self.add(&b.neg())}
    pub fn mul(&self,b:&Self)->KernelResult<Self>{
        self.same(b)?;
        Self::with_domain(self.numer.mul(&b.numer)?,self.denom.mul(&b.denom)?,self.guards(b))
    }
    pub fn div(&self,b:&Self)->KernelResult<Self>{
        self.same(b)?;
        if b.numer.is_zero(){return Err(KernelError::DivisionByZero);}
        let mut guards=self.guards(b);
        if !b.numer.is_nonzero_constant(){guards.insert(b.numer.monic());}
        Self::with_domain(self.numer.mul(&b.denom)?,self.denom.mul(&b.numer)?,guards)
    }
    pub fn pow(&self,k:u32)->KernelResult<Self>{
        Self::with_domain(self.numer.pow(k)?,self.denom.pow(k)?,self.excluded.clone())
    }
    pub fn diff(&self,var:usize)->KernelResult<Self>{
        let n=self.numer.diff(var)?.mul(&self.denom)?.sub(&self.numer.mul(&self.denom.diff(var)?)?)?;
        Self::with_domain(n,self.denom.pow(2)?,self.excluded.clone())
    }
    pub fn equals_algebraically(&self,b:&Self)->KernelResult<bool>{
        self.same(b)?;
        Ok(self.numer.mul(&b.denom)?==b.numer.mul(&self.denom)?)
    }
    pub fn evaluate(&self,values:&[S])->KernelResult<S>{
        for p in &self.excluded {if p.evaluate(values)?.is_zero(){return Err(KernelError::DomainSingularity(format!("{p} = 0")));}}
        self.numer.evaluate(values)?.div(&self.denom.evaluate(values)?)
    }
}
impl fmt::Display for RationalFunction{
    fn fmt(&self,f:&mut fmt::Formatter<'_>)->fmt::Result{write!(f,"({})/({})",self.numer,self.denom)}
}
