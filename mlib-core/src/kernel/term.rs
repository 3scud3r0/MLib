//! Deterministically indexed hash-consed syntax DAG.
//! Hash-cons equality is syntactic (within one arena); mathematical equivalence
//! is decided by the exact normalizer, never by raw node-ID comparison.
use crate::kernel::{KernelError,KernelResult};
use crate::kernel::rational::ExactScalar;
use std::collections::HashMap;

pub type TermId=usize;

#[derive(Clone,Debug,PartialEq,Eq,Hash)]
pub enum TermNode {
    Const(ExactScalar),
    Var(usize),
    Add(TermId,TermId),
    Sub(TermId,TermId),
    Mul(TermId,TermId),
    Div(TermId,TermId),
    Pow(TermId,u32),
    PartialDeriv{target:TermId,var_index:usize},
    PoissonBracket{space_id:usize,f:TermId,g:TermId},
    LieBasis{algebra_id:usize,index:usize},
    LieBracket{algebra_id:usize,x:TermId,y:TermId},
    ExteriorBasis{var_index:usize},
    ExteriorWedge(TermId,TermId),
    ExteriorDerivative(TermId),
}

#[derive(Clone,Debug)]
pub struct TermArena{
    nodes:Vec<TermNode>,
    indices:HashMap<TermNode,TermId>,
    max_nodes:usize,
}
impl Default for TermArena{fn default()->Self{Self::new(100_000)}}
impl TermArena{
    pub fn new(max_nodes:usize)->Self{Self{nodes:Vec::new(),indices:HashMap::new(),max_nodes}}
    pub fn len(&self)->usize{self.nodes.len()}
    pub fn is_empty(&self)->bool{self.nodes.is_empty()}
    pub fn get(&self,id:TermId)->KernelResult<&TermNode>{self.nodes.get(id).ok_or(KernelError::InvalidIndex(id))}
    pub fn intern(&mut self,node:TermNode)->KernelResult<TermId>{
        if let Some(id)=self.indices.get(&node){return Ok(*id);}
        if self.nodes.len()>=self.max_nodes{return Err(KernelError::ResourceLimit("arena excede capacidade".into()));}
        let child=|id:usize| if id>=self.nodes.len(){Err(KernelError::InvalidIndex(id))}else{Ok(())};
        match &node{
            TermNode::Add(a,b)|TermNode::Sub(a,b)|TermNode::Mul(a,b)|TermNode::Div(a,b)
            |TermNode::ExteriorWedge(a,b)=>{child(*a)?;child(*b)?;},
            TermNode::LieBracket{x,y,..}=>{child(*x)?;child(*y)?;},
            TermNode::PoissonBracket{f,g,..}=>{child(*f)?;child(*g)?;},
            TermNode::Pow(a,n)=>{child(*a)?;if *n>100_000{return Err(KernelError::ResourceLimit("potência > 100000".into()));}},
            TermNode::PartialDeriv{target,..}|TermNode::ExteriorDerivative(target)=>child(*target)?,
            _=>(),
        }
        let id=self.nodes.len();self.nodes.push(node.clone());self.indices.insert(node,id);Ok(id)
    }
    pub fn constant(&mut self,v:i64)->KernelResult<TermId>{self.intern(TermNode::Const(ExactScalar::from_i64(v)))}
    pub fn var(&mut self,index:usize)->KernelResult<TermId>{self.intern(TermNode::Var(index))}
}
