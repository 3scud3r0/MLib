use mlib_core::{Environment,TermArena,TermNode,TypeChecker,LieAlgebra,ExactScalar as S};
use mlib_core::kernel::canonical::{Normalizer,NormalizedValue};
use mlib_core::kernel::KernelError;

fn so3()->LieAlgebra{
    let mut c=vec![S::zero();27];
    let values=[(0,1,2,1),(1,0,2,-1),(1,2,0,1),(2,1,0,-1),(2,0,1,1),(0,2,1,-1)];
    for (i,j,k,v) in values{c[(i*3+j)*3+k]=S::from_i64(v);}
    LieAlgebra::new(3,c).unwrap()
}
#[test]
fn valid_so3_has_jacobi_certificate(){
    let env=Environment::new();let a=TermArena::default();
    let cert=TypeChecker::new(&env,&a).verify_lie_algebra(&so3()).unwrap();
    assert_eq!(cert.digest_hex().len(),64);
}
#[test]
fn bogus_structure_constants_are_rejected(){
    let mut c=vec![S::zero();64];
    // [e0,e1]=e0 and [e2,e3]=e1: the (0,2,3) Jacobi equation fails.
    for (i,j,k,v) in [(0,1,0,1),(1,0,0,-1),(2,3,1,1),(3,2,1,-1)]{
        c[(i*4+j)*4+k]=S::from_i64(v);
    }
    let bad=LieAlgebra::new(4,c).unwrap();
    assert!(matches!(bad.check_jacobi(),Err(KernelError::NonZeroResidual(_))));
}
#[test]
fn so3_quadratic_casimir(){
    let mut arena=TermArena::default();let x=(0..3).map(|i|arena.var(i).unwrap()).collect::<Vec<_>>();
    let xs=x.into_iter().map(|id|arena.intern(TermNode::Pow(id,2)).unwrap()).collect::<Vec<_>>();
    let first=arena.intern(TermNode::Add(xs[0],xs[1])).unwrap();
    let candidate=arena.intern(TermNode::Add(first,xs[2])).unwrap();
    let env=Environment::new();let cert=TypeChecker::new(&env,&arena).verify_casimir(&so3(),candidate).unwrap();
    assert!(cert.domain_exclusions().is_empty());
}
#[test]
fn so3_linear_coordinate_not_casimir(){
    let mut a=TermArena::default();let x=a.var(0).unwrap();
    let env=Environment::new();
    assert!(matches!(TypeChecker::new(&env,&a).verify_casimir(&so3(),x),Err(KernelError::NonZeroResidual(_))));
}
#[test]
fn lie_bracket_of_basis_vectors(){
    let (env,algebra_id)=Environment::new().with_lie_algebra(so3()).unwrap();
    let mut arena=TermArena::default();
    let x=arena.intern(TermNode::LieBasis{algebra_id,index:0}).unwrap();
    let y=arena.intern(TermNode::LieBasis{algebra_id,index:1}).unwrap();
    let bracket=arena.intern(TermNode::LieBracket{algebra_id,x,y}).unwrap();
    let mut n=Normalizer::new(&arena,3,env.lie_algebras()).unwrap();
    match n.normalize(bracket).unwrap(){
        NormalizedValue::LieVector{coefficients,..}=>{
            assert!(coefficients[0].is_zero());assert!(coefficients[1].is_zero());assert!(coefficients[2].is_one());
        },_=>panic!("expected Lie vector")
    }
}
#[test]
fn exterior_square_is_zero_and_antisymmetric(){
    let mut arena=TermArena::default();
    let dx=arena.intern(TermNode::ExteriorBasis{var_index:0}).unwrap();
    let dy=arena.intern(TermNode::ExteriorBasis{var_index:1}).unwrap();
    let dxdy=arena.intern(TermNode::ExteriorWedge(dx,dy)).unwrap();
    let dydx=arena.intern(TermNode::ExteriorWedge(dy,dx)).unwrap();
    let sum=arena.intern(TermNode::Add(dxdy,dydx)).unwrap();
    let repeated=arena.intern(TermNode::ExteriorWedge(dx,dx)).unwrap();
    let env=Environment::new();
    for term in [sum,repeated]{
        match Normalizer::new(&arena,2,env.lie_algebras()).unwrap().normalize(term).unwrap(){
            NormalizedValue::Form(f)=>assert!(f.is_zero()),_=>panic!("expected form")
        }
    }
}
#[test]
fn exterior_d_squared_is_zero(){
    let mut arena=TermArena::default();let x=arena.var(0).unwrap();let y=arena.var(1).unwrap();
    let xy=arena.intern(TermNode::Mul(x,y)).unwrap();
    let d=arena.intern(TermNode::ExteriorDerivative(xy)).unwrap();
    let dd=arena.intern(TermNode::ExteriorDerivative(d)).unwrap();
    let env=Environment::new();
    match Normalizer::new(&arena,2,env.lie_algebras()).unwrap().normalize(dd).unwrap(){
        NormalizedValue::Form(f)=>assert!(f.is_zero()),_=>panic!("expected form")
    }
}
