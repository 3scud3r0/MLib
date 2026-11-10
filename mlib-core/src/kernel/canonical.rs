//! Deep exact normalization (not Lean's general definitional WHNF).
//! Unsupported operations fail closed. Every rational expression carries
//! exclusions inherited from its unnormalized denominators.
use crate::kernel::{KernelError,KernelResult};
use crate::kernel::term::{TermArena,TermId,TermNode};
use crate::kernel::ring::{Polynomial,RationalFunction as RF};
use crate::kernel::types::LieAlgebra;
use std::collections::{BTreeMap,BTreeSet,HashMap};

#[derive(Clone,Debug)]
pub struct NormalizationLimits{
    pub max_depth:usize,
    pub max_terms:usize,
    pub max_total_degree:u64,
}
impl Default for NormalizationLimits{fn default()->Self{Self{max_depth:256,max_terms:16384,max_total_degree:1024}}}

#[derive(Clone,Debug)]
pub struct ExteriorForm{
    dimension:usize,
    degree:usize,
    coefficients:BTreeMap<Vec<usize>,RF>,
    domain:BTreeSet<Polynomial>,
}
impl ExteriorForm {
    pub fn zero(dimension:usize,degree:usize)->Self{Self{dimension,degree,coefficients:BTreeMap::new(),domain:BTreeSet::new()}}
    pub fn basis(dimension:usize,index:usize)->KernelResult<Self>{
        if index>=dimension{return Err(KernelError::InvalidIndex(index));}
        let mut out=Self::zero(dimension,1);
        out.coefficients.insert(vec![index],RF::one(dimension));
        Ok(out)
    }
    pub fn from_scalar(r:RF)->Self{
        let mut out=Self::zero(r.nvars(),0);
        out.domain=r.exclusions().clone();
        if !r.is_zero(){out.coefficients.insert(Vec::new(),r);}
        out
    }
    pub fn degree(&self)->usize{self.degree}
    pub fn coefficients(&self)->&BTreeMap<Vec<usize>,RF>{&self.coefficients}
    pub fn is_zero(&self)->bool{self.coefficients.is_empty()}
    fn conform(&self,b:&Self)->KernelResult<()>{
        if self.dimension!=b.dimension||self.degree!=b.degree{
            return Err(KernelError::TypeError("formas exteriores com graus/dimensões incompatíveis".into()));
        }
        Ok(())
    }
    pub fn add(&self,b:&Self)->KernelResult<Self>{
        self.conform(b)?;
        let mut result=self.clone();
        result.domain.extend(b.domain.iter().cloned());
        for (keys,rf) in &b.coefficients{
            let prev=result.coefficients.remove(keys).unwrap_or_else(||RF::zero(self.dimension));
            let sum=prev.add(rf)?;
            if !sum.is_zero(){result.coefficients.insert(keys.clone(),sum);}
        }
        Ok(result)
    }
    pub fn neg(&self)->Self{
        Self{dimension:self.dimension,degree:self.degree,coefficients:self.coefficients.iter().map(|(k,v)|(k.clone(),v.neg())).collect(),domain:self.domain.clone()}
    }
    pub fn sub(&self,b:&Self)->KernelResult<Self>{self.add(&b.neg())}
    pub fn scale(&self,scalar:&RF)->KernelResult<Self>{
        if self.dimension!=scalar.nvars(){return Err(KernelError::DimensionMismatch("escalar de forma".into()));}
        let mut out=Self::zero(self.dimension,self.degree);
        out.domain.extend(self.domain.iter().cloned());out.domain.extend(scalar.exclusions().iter().cloned());
        for (key,v) in &self.coefficients{let c=v.mul(scalar)?;if !c.is_zero(){out.coefficients.insert(key.clone(),c);}}
        Ok(out)
    }
    pub fn wedge(&self,b:&Self)->KernelResult<Self>{
        if self.dimension!=b.dimension{return Err(KernelError::DimensionMismatch("wedge".into()));}
        let mut out=Self::zero(self.dimension,self.degree+b.degree);
        out.domain.extend(self.domain.iter().cloned());out.domain.extend(b.domain.iter().cloned());
        for (a,ca) in &self.coefficients {for (b,cb) in &b.coefficients {
            if a.iter().any(|i|b.contains(i)){continue;}
            let inversions=a.iter().map(|i|b.iter().filter(|j|*j<i).count()).sum::<usize>();
            let mut keys=a.clone();keys.extend_from_slice(b);keys.sort_unstable();
            let mut coeff=ca.mul(cb)?;
            if inversions%2==1{coeff=coeff.neg();}
            let previous=out.coefficients.remove(&keys).unwrap_or_else(||RF::zero(self.dimension));
            let sum=previous.add(&coeff)?;
            if !sum.is_zero(){out.coefficients.insert(keys,sum);}
        }}
        Ok(out)
    }
    pub fn exterior_derivative(&self)->KernelResult<Self>{
        let mut out=Self::zero(self.dimension,self.degree+1);
        out.domain.extend(self.domain.iter().cloned());
        for (indices,coeff) in &self.coefficients {
            for var in 0..self.dimension{
                let derivative=coeff.diff(var)?;
                if derivative.is_zero(){continue;}
                let basis=Self::basis(self.dimension,var)?;
                let mut as_form=Self::zero(self.dimension,self.degree);
                as_form.coefficients.insert(indices.clone(),derivative);
                out=out.add(&basis.wedge(&as_form)?)?;
            }
        }
        Ok(out)
    }
    pub fn domain(&self)->BTreeSet<Polynomial>{
        let mut all=self.domain.clone();
        all.extend(self.coefficients.values().flat_map(|x|x.exclusions().iter().cloned()));
        all
    }
}

#[derive(Clone,Debug)]
pub enum NormalizedValue {
    Scalar(RF),
    LieVector{algebra_id:usize,coefficients:Vec<RF>},
    Form(ExteriorForm),
}
impl NormalizedValue{
    pub fn scalar(self)->KernelResult<RF>{
        match self {Self::Scalar(v)=>Ok(v),_=>Err(KernelError::TypeError("expressão não escalar".into()))}
    }
    pub fn domain(&self)->BTreeSet<Polynomial>{
        match self{
            Self::Scalar(x)=>x.exclusions().clone(),
            Self::LieVector{coefficients,..}=>coefficients.iter().flat_map(|c|c.exclusions().iter().cloned()).collect(),
            Self::Form(f)=>f.domain(),
        }
    }
    fn add(self,b:Self)->KernelResult<Self>{
        match (self,b){
            (Self::Scalar(a),Self::Scalar(b))=>Ok(Self::Scalar(a.add(&b)?)),
            (Self::Form(a),Self::Form(b))=>Ok(Self::Form(a.add(&b)?)),
            (Self::LieVector{algebra_id:a,coefficients:x},Self::LieVector{algebra_id:b,coefficients:y}) if a==b=>{
                Ok(Self::LieVector{algebra_id:a,coefficients:x.iter().zip(y.iter()).map(|(i,j)|i.add(j)).collect::<KernelResult<Vec<_>>>()?})
            },
            _=>Err(KernelError::TypeError("soma entre tipos incompatíveis".into()))
        }
    }
    fn neg(self)->Self{
        match self{
            Self::Scalar(v)=>Self::Scalar(v.neg()),
            Self::Form(v)=>Self::Form(v.neg()),
            Self::LieVector{algebra_id,coefficients}=>Self::LieVector{algebra_id,coefficients:coefficients.into_iter().map(|x|x.neg()).collect()},
        }
    }
    fn sub(self,b:Self)->KernelResult<Self>{self.add(b.neg())}
    fn mul(self,b:Self)->KernelResult<Self>{
        match (self,b){
            (Self::Scalar(a),Self::Scalar(b))=>Ok(Self::Scalar(a.mul(&b)?)),
            (Self::Scalar(s),Self::Form(f))|(Self::Form(f),Self::Scalar(s))=>Ok(Self::Form(f.scale(&s)?)),
            (Self::Scalar(s),Self::LieVector{algebra_id,coefficients})|(Self::LieVector{algebra_id,coefficients},Self::Scalar(s))=>{
                Ok(Self::LieVector{algebra_id,coefficients:coefficients.iter().map(|v|v.mul(&s)).collect::<KernelResult<Vec<_>>>()?})
            },
            _=>Err(KernelError::TypeError("multiplicação de tensores não definida; use wedge".into()))
        }
    }
    fn div(self,b:Self)->KernelResult<Self>{
        let d=b.scalar()?;
        match self{
            Self::Scalar(s)=>Ok(Self::Scalar(s.div(&d)?)),
            Self::Form(f)=>Ok(Self::Form(f.scale(&RF::one(d.nvars()).div(&d)?)?)),
            Self::LieVector{algebra_id,coefficients}=>Ok(Self::LieVector{algebra_id,coefficients:coefficients.iter().map(|v|v.div(&d)).collect::<KernelResult<Vec<_>>>()?}),
        }
    }
}

pub fn poisson(f:&RF,g:&RF,pairs:usize)->KernelResult<RF>{
    if pairs==0||pairs.checked_mul(2)!=Some(f.nvars())||f.nvars()!=g.nvars(){
        return Err(KernelError::DimensionMismatch("Poisson exige 2n variáveis".into()));
    }
    let mut result=RF::zero(f.nvars());
    for i in 0..pairs{
        result=result.add(&f.diff(i)?.mul(&g.diff(pairs+i)?)?)?;
        result=result.sub(&f.diff(pairs+i)?.mul(&g.diff(i)?)?)?;
    }
    Ok(result)
}

pub struct Normalizer<'a>{
    arena:&'a TermArena,
    nvars:usize,
    lie_algebras:&'a [LieAlgebra],
    limits:NormalizationLimits,
    cache:HashMap<TermId,NormalizedValue>,
}
impl<'a> Normalizer<'a>{
    pub fn new(arena:&'a TermArena,nvars:usize,lie_algebras:&'a [LieAlgebra])->KernelResult<Self>{
        if nvars>128{return Err(KernelError::ResourceLimit("mais de 128 variáveis".into()));}
        Ok(Self{arena,nvars,lie_algebras,limits:NormalizationLimits::default(),cache:HashMap::new()})
    }
    pub fn limits(mut self,limits:NormalizationLimits)->Self{self.limits=limits;self}
    pub fn normalize(&mut self,id:TermId)->KernelResult<NormalizedValue>{self.visit(id,0)}
    fn visit(&mut self,id:TermId,depth:usize)->KernelResult<NormalizedValue>{
        if depth>self.limits.max_depth{return Err(KernelError::ResourceLimit("profundidade do termo".into()));}
        if let Some(v)=self.cache.get(&id){return Ok(v.clone());}
        let node=self.arena.get(id)?.clone();
        let value=match node{
            TermNode::Const(c)=>NormalizedValue::Scalar(RF::from_poly(Polynomial::constant(self.nvars,c))),
            TermNode::Var(i)=>NormalizedValue::Scalar(RF::from_poly(Polynomial::var(self.nvars,i)?)),
            TermNode::Add(a,b)=>self.visit(a,depth+1)?.add(self.visit(b,depth+1)?)?,
            TermNode::Sub(a,b)=>self.visit(a,depth+1)?.sub(self.visit(b,depth+1)?)?,
            TermNode::Mul(a,b)=>self.visit(a,depth+1)?.mul(self.visit(b,depth+1)?)?,
            TermNode::Div(a,b)=>self.visit(a,depth+1)?.div(self.visit(b,depth+1)?)?,
            TermNode::Pow(a,p)=>NormalizedValue::Scalar(self.visit(a,depth+1)?.scalar()?.pow(p)?),
            TermNode::PartialDeriv{target,var_index}=>NormalizedValue::Scalar(self.visit(target,depth+1)?.scalar()?.diff(var_index)?),
            TermNode::PoissonBracket{space_id,f,g}=>{
                let a=self.visit(f,depth+1)?.scalar()?;
                let b=self.visit(g,depth+1)?.scalar()?;
                NormalizedValue::Scalar(poisson(&a,&b,space_id)?)
            },
            TermNode::LieBasis{algebra_id,index}=>{
                let a=self.lie_algebras.get(algebra_id).ok_or(KernelError::InvalidIndex(algebra_id))?;
                if index>=a.dim(){return Err(KernelError::InvalidIndex(index));}
                let mut components=vec![RF::zero(self.nvars);a.dim()];
                components[index]=RF::one(self.nvars);
                NormalizedValue::LieVector{algebra_id,coefficients:components}
            },
            TermNode::LieBracket{algebra_id,x,y}=>{
                let a=self.lie_algebras.get(algebra_id).ok_or(KernelError::InvalidIndex(algebra_id))?;
                let (ax,vx)=match self.visit(x,depth+1)?{NormalizedValue::LieVector{algebra_id,coefficients}=>(algebra_id,coefficients),_=>return Err(KernelError::TypeError("colchete Lie requer geradores".into()))};
                let (ay,vy)=match self.visit(y,depth+1)?{NormalizedValue::LieVector{algebra_id,coefficients}=>(algebra_id,coefficients),_=>return Err(KernelError::TypeError("colchete Lie requer geradores".into()))};
                if ax!=algebra_id||ay!=algebra_id{return Err(KernelError::TypeError("álgebras de Lie diferentes".into()));}
                let mut out=vec![RF::zero(self.nvars);a.dim()];
                for i in 0..a.dim(){for j in 0..a.dim(){for (k,entry) in out.iter_mut().enumerate().take(a.dim()){
                    let coef=RF::from_poly(Polynomial::constant(self.nvars,a.c(i,j,k).clone()));
                    *entry=entry.add(&vx[i].mul(&vy[j])?.mul(&coef)?)?;
                }}}
                NormalizedValue::LieVector{algebra_id,coefficients:out}
            },
            TermNode::ExteriorBasis{var_index}=>NormalizedValue::Form(ExteriorForm::basis(self.nvars,var_index)?),
            TermNode::ExteriorWedge(x,y)=>{
                let fx=as_form(self.visit(x,depth+1)?);
                let fy=as_form(self.visit(y,depth+1)?);
                NormalizedValue::Form(fx?.wedge(&fy?)?)
            },
            TermNode::ExteriorDerivative(x)=>{
                let f=as_form(self.visit(x,depth+1)?)?;
                NormalizedValue::Form(f.exterior_derivative()?)
            },
        };
        let termcount=match &value{
            NormalizedValue::Scalar(r)=>r.numerator().terms().len()+r.denominator().terms().len(),
            NormalizedValue::LieVector{coefficients,..}=>coefficients.iter().map(|r|r.numerator().terms().len()+r.denominator().terms().len()).sum(),
            NormalizedValue::Form(f)=>f.coefficients.values().map(|r|r.numerator().terms().len()+r.denominator().terms().len()).sum(),
        };
        if termcount>self.limits.max_terms{return Err(KernelError::ResourceLimit("quantidade de monômios".into()));}
        let maxdeg=match &value{
            NormalizedValue::Scalar(r)=>r.numerator().degree().max(r.denominator().degree()),
            _=>0,
        };
        if maxdeg>self.limits.max_total_degree{return Err(KernelError::ResourceLimit("grau normalizado".into()));}
        self.cache.insert(id,value.clone());
        Ok(value)
    }
}
fn as_form(v:NormalizedValue)->KernelResult<ExteriorForm>{
    match v{NormalizedValue::Scalar(s)=>Ok(ExteriorForm::from_scalar(s)),NormalizedValue::Form(f)=>Ok(f),_=>Err(KernelError::TypeError("vetores de Lie não são formas exteriores".into()))}
}
