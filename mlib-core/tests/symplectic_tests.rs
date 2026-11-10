use mlib_core::{Environment,TypeChecker,TermArena,TermNode,ExactScalar as S,Polynomial as P};
use mlib_core::kernel::linear_algebra::{bareiss_determinant,positive_definite_ldlt,rank};
use mlib_core::kernel::KernelError;

#[test]
fn exact_symplectic_kick(){
    let mut a=TermArena::default();let q=a.var(0).unwrap();let p=a.var(1).unwrap();
    let q3=a.intern(TermNode::Pow(q,3)).unwrap();let kick=a.intern(TermNode::Sub(p,q3)).unwrap();
    let env=Environment::new();let checker=TypeChecker::new(&env,&a);
    let cert=checker.verify_symplectic_map(1,&[q,kick]).unwrap();
    assert!(cert.domain_exclusions().is_empty());
}
#[test]
fn non_symplectic_scaling_rejected(){
    let mut a=TermArena::default();let q=a.var(0).unwrap();let p=a.var(1).unwrap();
    let two=a.constant(2).unwrap();let scaled=a.intern(TermNode::Mul(two,p)).unwrap();
    let env=Environment::new();let checker=TypeChecker::new(&env,&a);
    assert!(matches!(checker.verify_symplectic_map(1,&[q,scaled]),Err(KernelError::NonZeroResidual(_))));
}
#[test]
fn bareiss_row_exchange_exact(){
    let m=vec![vec![S::from_i64(0),S::from_i64(1)],vec![S::from_i64(1),S::from_i64(0)]];
    assert_eq!(bareiss_determinant(&m).unwrap(),S::from_i64(-1));
}
#[test]
fn ldlt_positive_reconstruction(){
    let m=vec![vec![S::from_i64(2),S::from_i64(1)],vec![S::from_i64(1),S::from_i64(2)]];
    let cert=positive_definite_ldlt(&m).unwrap();
    assert_eq!(cert.diagonal[1],S::parse("3","2").unwrap());
    let env=Environment::new();let arena=TermArena::default();
    assert!(TypeChecker::new(&env,&arena).verify_positive_gram(&m).is_ok());
}
#[test]
fn reject_indefinite_symmetric_gram(){
    let m=vec![vec![S::from_i64(1),S::from_i64(2)],vec![S::from_i64(2),S::from_i64(1)]];
    assert!(positive_definite_ldlt(&m).is_err());
}
#[test]
fn reject_nonsymmetric_gram(){
    let m=vec![vec![S::from_i64(1),S::from_i64(2)],vec![S::from_i64(0),S::from_i64(1)]];
    assert!(positive_definite_ldlt(&m).is_err());
}
#[test]
fn rank_of_singular_matrix(){
    let m=vec![vec![S::from_i64(1),S::from_i64(2)],vec![S::from_i64(2),S::from_i64(4)]];
    assert_eq!(rank(&m).unwrap(),1);
    assert_eq!(bareiss_determinant(&m).unwrap(),S::zero());
}
#[test]
fn polynomial_identity_simplifies_exactly(){
    let x=P::var(2,0).unwrap();let y=P::var(2,1).unwrap();
    let expr=x.add(&y).unwrap().pow(2).unwrap();
    let expected=x.pow(2).unwrap().add(&x.mul(&y).unwrap().scale(&S::from_i64(2))).unwrap().add(&y.pow(2).unwrap()).unwrap();
    assert_eq!(expr,expected);
}
#[test]
fn rational_gcd_disjoint_and_repeated_factors(){
    let x=P::var(2,0).unwrap();let y=P::var(2,1).unwrap();
    let f=x.add(&y).unwrap();
    let a=f.pow(3).unwrap().mul(&x.add(&P::one(2)).unwrap()).unwrap();
    let b=f.pow(2).unwrap().mul(&y.add(&P::one(2)).unwrap()).unwrap();
    assert_eq!(a.gcd(&b).unwrap(),f.pow(2).unwrap().monic());
}
