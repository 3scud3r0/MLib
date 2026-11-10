use mlib_core::kernel::{KernelError,KernelResult};
use mlib_core::{ExactScalar as S,TermArena,TermNode,TypeChecker,Environment,Polynomial as P,RationalFunction as RF};

fn make(arena:&mut TermArena,a:usize,b:usize,op:&str)->usize{
    arena.intern(match op{
        "+"=>TermNode::Add(a,b),"-"=>TermNode::Sub(a,b),"*"=>TermNode::Mul(a,b),"/"=>TermNode::Div(a,b),_=>panic!("invalid test operator")}).unwrap()
}
#[test]
fn forged_conservation_rejected(){
    let mut a=TermArena::default();let q=a.var(0).unwrap();let p=a.var(1).unwrap();
    let p2=a.intern(TermNode::Pow(p,2)).unwrap();let q4=a.intern(TermNode::Pow(q,4)).unwrap();
    let two=a.constant(2).unwrap();let four=a.constant(4).unwrap();
    let t=make(&mut a,p2,two,"/");let v=make(&mut a,q4,four,"/");let h=make(&mut a,t,v,"+");
    let env=Environment::new();let checker=TypeChecker::new(&env,&a);
    let err=checker.verify_conservation(1,h,q).unwrap_err();
    assert!(matches!(err,KernelError::NonZeroResidual(_)),"{err:?}");
}
#[test]
fn harmonic_energy_is_conserved(){
    let mut a=TermArena::default();let q=a.var(0).unwrap();let p=a.var(1).unwrap();
    let q2=a.intern(TermNode::Pow(q,2)).unwrap();let p2=a.intern(TermNode::Pow(p,2)).unwrap();
    let sum=make(&mut a,q2,p2,"+");let two=a.constant(2).unwrap();let h=make(&mut a,sum,two,"/");
    let env=Environment::new();let checker=TypeChecker::new(&env,&a);
    let cert=checker.verify_conservation(1,h,h).unwrap();
    assert!(cert.domain_exclusions().is_empty());
    assert!(cert.to_lean4_code().unwrap().contains("by\n  ring"));
    assert_eq!(cert.digest_hex().len(),64);
}
#[test]
fn angular_momentum_quartic_potential(){
    let mut a=TermArena::default();
    let ids=(0..4).map(|i|a.var(i).unwrap()).collect::<Vec<_>>();
    let qx2=a.intern(TermNode::Pow(ids[0],2)).unwrap();let qy2=a.intern(TermNode::Pow(ids[1],2)).unwrap();
    let px2=a.intern(TermNode::Pow(ids[2],2)).unwrap();let py2=a.intern(TermNode::Pow(ids[3],2)).unwrap();
    let q2=make(&mut a,qx2,qy2,"+");
    let p2=make(&mut a,px2,py2,"+");
    let sum=make(&mut a,q2,p2,"+");let two=a.constant(2).unwrap();let four=a.constant(4).unwrap();
    let kinetic=make(&mut a,sum,two,"/");let r4=a.intern(TermNode::Pow(q2,2)).unwrap();let potential=make(&mut a,r4,four,"/");
    let h=make(&mut a,kinetic,potential,"+");
    let l0=make(&mut a,ids[0],ids[3],"*");let l1=make(&mut a,ids[1],ids[2],"*");
    let l=make(&mut a,l0,l1,"-");
    let env=Environment::new();let checker=TypeChecker::new(&env,&a);
    assert!(checker.verify_conservation(2,h,l).is_ok());
}
#[test]
fn cancelled_denominator_keeps_original_domain(){
    let mut a=TermArena::default();let x=a.var(0).unwrap();let one=a.constant(1).unwrap();
    let x_minus_one=make(&mut a,x,one,"-");
    let x2=a.intern(TermNode::Pow(x,2)).unwrap();let numerator=make(&mut a,x2,one,"-");
    let expr=make(&mut a,numerator,x_minus_one,"/");
    let env=Environment::new();let checker=TypeChecker::new(&env,&a);
    let f=checker.normalize_scalar(expr,1).unwrap();
    assert_eq!(f.evaluate(&[S::from_i64(2)]).unwrap(),S::from_i64(3));
    assert!(matches!(f.evaluate(&[S::from_i64(1)]),Err(KernelError::DomainSingularity(_))));
    assert_eq!(f.exclusions().len(),1);
}
#[test]
fn zero_over_zero_denominator_rejected(){
    let a=P::zero(1);assert!(matches!(RF::new(a.clone(),a),Err(KernelError::DivisionByZero)));
}
#[test]
fn bit_identical_interning_and_bounds(){
    let mut a=TermArena::new(3);let x=a.var(0).unwrap();let y=a.var(1).unwrap();
    assert_eq!(a.var(0).unwrap(),x);
    assert!(matches!(a.intern(TermNode::Add(7,y)),Err(KernelError::InvalidIndex(7))));
    a.intern(TermNode::Add(x,y)).unwrap();
    assert!(matches!(a.constant(4),Err(KernelError::ResourceLimit(_))));
}
#[test]
fn no_arithmetic_float_coercion(){
    assert!(S::parse("1","0").is_err());
    assert!(S::parse("1.5","1").is_err());
}
#[test]
fn hash_depends_on_claim_contents_not_ids(){
    let mut a=TermArena::default();let q=a.var(0).unwrap();let p=a.var(1).unwrap();
    let h=make(&mut a,q,p,"+");
    let env=Environment::new();let c=TypeChecker::new(&env,&a);
    let a1=c.verify_conservation(1,h,h).unwrap();
    let a2=c.verify_conservation(1,h,h).unwrap();
    assert_eq!(a1.digest_hex(),a2.digest_hex());
    assert_ne!(a1.digest_hex(),"00".repeat(32));
}
#[test]
fn restricted_domain_zero_bracket_has_guards(){
    let mut a=TermArena::default();let q=a.var(0).unwrap();let one=a.constant(1).unwrap();
    let h=make(&mut a,q,q,"/");
    let env=Environment::new();let cert=TypeChecker::new(&env,&a).verify_conservation(1,h,one).unwrap();
    assert_eq!(cert.domain_exclusions().len(),1);
    assert!(cert.to_lean4_code().is_none());
}
#[test]
fn no_variable_overflow(){
    let mut a=TermArena::default();let x=a.var(9).unwrap();
    let env=Environment::new();assert!(matches!(TypeChecker::new(&env,&a).normalize_scalar(x,2),Err(KernelError::InvalidIndex(9))));
}
#[test]
fn result_error_types_are_strict()->KernelResult<()>{
    let x=P::var(2,0)?;let y=P::var(2,1)?;
    let two=P::constant(2,S::from_i64(2));
    let common=x.add(&y)?;
    let p=common.mul(&x.add(&two)?)?;
    let q=common.mul(&y.add(&two)?)?;
    assert_eq!(p.gcd(&q)?,common.monic());
    Ok(())
}
