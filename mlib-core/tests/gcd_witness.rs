//! The proposed GCD is untrusted and must be greatest, not just a divisor.
use mlib_core::{Environment,TermArena,TermNode,TypeChecker};
use mlib_core::kernel::KernelError;

#[test]
fn correct_polynomial_gcd_hint_is_certified(){
    let mut arena=TermArena::default();
    let x=arena.var(0).unwrap();let y=arena.var(1).unwrap();
    let common=arena.intern(TermNode::Add(x,y)).unwrap();
    let a=arena.intern(TermNode::Mul(common,x)).unwrap();
    let b=arena.intern(TermNode::Mul(common,y)).unwrap();
    let env=Environment::new();
    let result=TypeChecker::new(&env,&arena).verify_gcd_hint(2,a,b,common).unwrap();
    assert!(format!("{:?}",result.claim()).contains("IsGcdPolynomial"));
    assert_eq!(result.digest_hex().len(),64);
}

#[test]
fn unit_hint_is_rejected_when_a_nonunit_gcd_exists(){
    let mut arena=TermArena::default();
    let x=arena.var(0).unwrap();let y=arena.var(1).unwrap();
    let shared=arena.intern(TermNode::Add(x,y)).unwrap();
    let a=arena.intern(TermNode::Mul(shared,x)).unwrap();
    let b=arena.intern(TermNode::Mul(shared,y)).unwrap();
    let unit=arena.constant(1).unwrap();
    let env=Environment::new();
    assert!(matches!(TypeChecker::new(&env,&arena).verify_gcd_hint(2,a,b,unit),Err(KernelError::InvalidCertificate(_))));
}

#[test]
fn nonexistent_common_divisor_is_rejected(){
    let mut arena=TermArena::default();
    let x=arena.var(0).unwrap();let y=arena.var(1).unwrap();
    let env=Environment::new();
    assert!(matches!(TypeChecker::new(&env,&arena).verify_gcd_hint(2,x,y,x),Err(KernelError::InvalidCertificate(_))));
}

#[test]
fn canceled_domain_exclusion_prevents_global_gcd_certificate(){
    let mut arena=TermArena::default();
    let x=arena.var(0).unwrap();
    let candidate=arena.intern(TermNode::Div(x,x)).unwrap();
    let env=Environment::new();
    assert!(matches!(TypeChecker::new(&env,&arena).verify_gcd_hint(1,x,x,candidate),Err(KernelError::DomainSingularity(_))));
}

#[test]
fn zero_zero_gcd_is_not_a_certified_function(){
    let mut arena=TermArena::default();
    let zero=arena.constant(0).unwrap();let one=arena.constant(1).unwrap();
    let env=Environment::new();
    assert!(matches!(TypeChecker::new(&env,&arena).verify_gcd_hint(1,zero,zero,one),Err(KernelError::InvalidCertificate(_))));
}
