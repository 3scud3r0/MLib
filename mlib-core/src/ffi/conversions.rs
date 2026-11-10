//! Strict JSON AST decoder; no Python eval or floating-point coercion.
use crate::kernel::term::{TermArena,TermId,TermNode};
use crate::kernel::rational::ExactScalar;
use crate::kernel::{KernelError,KernelResult};
use serde::Deserialize;

#[derive(Deserialize,Debug)]
#[serde(tag="op",rename_all="snake_case",deny_unknown_fields)]
pub enum JsonTerm {
    Const{num:String,den:String},
    Var{index:usize},
    Add{left:Box<JsonTerm>,right:Box<JsonTerm>},
    Sub{left:Box<JsonTerm>,right:Box<JsonTerm>},
    Mul{left:Box<JsonTerm>,right:Box<JsonTerm>},
    Div{left:Box<JsonTerm>,right:Box<JsonTerm>},
    Pow{base:Box<JsonTerm>,exponent:u32},
    PartialDeriv{target:Box<JsonTerm>,var_index:usize},
    PoissonBracket{pairs:usize,f:Box<JsonTerm>,g:Box<JsonTerm>},
    ExteriorBasis{var_index:usize},
    ExteriorWedge{left:Box<JsonTerm>,right:Box<JsonTerm>},
    ExteriorDerivative{target:Box<JsonTerm>},
    LieBasis{algebra_id:usize,index:usize},
    LieBracket{algebra_id:usize,left:Box<JsonTerm>,right:Box<JsonTerm>},
}
pub fn parse_json(json:&str)->KernelResult<JsonTerm>{
    if json.len()>2_000_000{return Err(KernelError::ResourceLimit("AST JSON > 2 MB".into()));}
    serde_json::from_str(json).map_err(|e|KernelError::TypeError(format!("JSON AST inválido: {e}")))
}
pub fn into_arena(term:&JsonTerm,arena:&mut TermArena,depth:usize)->KernelResult<TermId>{
    if depth>64{return Err(KernelError::ResourceLimit("AST JSON profundidade > 64".into()));}
    let next=depth+1;
    let n=match term{
        JsonTerm::Const{num,den}=>TermNode::Const(ExactScalar::parse(num,den)?),
        JsonTerm::Var{index}=>TermNode::Var(*index),
        JsonTerm::Add{left,right}=>TermNode::Add(into_arena(left,arena,next)?,into_arena(right,arena,next)?),
        JsonTerm::Sub{left,right}=>TermNode::Sub(into_arena(left,arena,next)?,into_arena(right,arena,next)?),
        JsonTerm::Mul{left,right}=>TermNode::Mul(into_arena(left,arena,next)?,into_arena(right,arena,next)?),
        JsonTerm::Div{left,right}=>TermNode::Div(into_arena(left,arena,next)?,into_arena(right,arena,next)?),
        JsonTerm::Pow{base,exponent}=>TermNode::Pow(into_arena(base,arena,next)?,*exponent),
        JsonTerm::PartialDeriv{target,var_index}=>TermNode::PartialDeriv{target:into_arena(target,arena,next)?,var_index:*var_index},
        JsonTerm::PoissonBracket{pairs,f,g}=>TermNode::PoissonBracket{space_id:*pairs,f:into_arena(f,arena,next)?,g:into_arena(g,arena,next)?},
        JsonTerm::ExteriorBasis{var_index}=>TermNode::ExteriorBasis{var_index:*var_index},
        JsonTerm::ExteriorWedge{left,right}=>TermNode::ExteriorWedge(into_arena(left,arena,next)?,into_arena(right,arena,next)?),
        JsonTerm::ExteriorDerivative{target}=>TermNode::ExteriorDerivative(into_arena(target,arena,next)?),
        JsonTerm::LieBasis{algebra_id,index}=>TermNode::LieBasis{algebra_id:*algebra_id,index:*index},
        JsonTerm::LieBracket{algebra_id,left,right}=>TermNode::LieBracket{algebra_id:*algebra_id,x:into_arena(left,arena,next)?,y:into_arena(right,arena,next)?},
    };
    arena.intern(n)
}
