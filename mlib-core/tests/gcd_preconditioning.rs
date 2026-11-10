//! Deterministic exact hot paths: no probabilistic Zippel shortcut is claimed.
use mlib_core::{ExactScalar as S, Polynomial, RationalFunction};
use mlib_core::kernel::KernelError;

fn v(n:usize,i:usize)->Polynomial{Polynomial::var(n,i).expect("valid variable")}

#[test]
fn multivariate_monomial_gcd_is_exact_in_eight_variables(){
    let n=8;
    let x=v(n,0);
    let y=v(n,7);
    let a=x.pow(10).unwrap().mul(&y.pow(3).unwrap()).unwrap();
    let b=x.pow(6).unwrap().mul(&y.pow(4).unwrap()).unwrap();
    let r=b.mul(&x.add(&Polynomial::one(n)).unwrap()).unwrap();
    let gcd=a.gcd(&r).unwrap();
    let expected=x.pow(6).unwrap().mul(&y.pow(3).unwrap()).unwrap();
    assert_eq!(gcd,expected);
    assert!(a.exact_div(&gcd).is_ok());
    assert!(r.exact_div(&gcd).is_ok());
}

#[test]
fn unit_and_equal_gcd_paths_are_exact(){
    let n=6;
    let p=v(n,0).pow(5).unwrap().add(&v(n,5).pow(3).unwrap()).unwrap();
    assert_eq!(p.gcd(&p).unwrap(),p.monic());
    assert_eq!(p.gcd(&Polynomial::constant(n,S::from_i64(17))).unwrap(),Polynomial::one(n));
}

#[test]
fn polynomial_only_rational_arithmetic_stays_in_polynomial_ring(){
    let n=7;
    let x=RationalFunction::from_poly(v(n,0));
    let y=RationalFunction::from_poly(v(n,6));
    let sum=x.add(&y).unwrap();
    let result=sum.mul(&sum).unwrap();
    assert!(result.denominator().is_one());
    assert!(result.exclusions().is_empty());
    assert_eq!(result.numerator(),&v(n,0).add(&v(n,6)).unwrap().pow(2).unwrap());
}

#[test]
fn canceled_rational_factor_retains_original_pole(){
    let x=v(1,0);
    let rational=RationalFunction::new(x.clone(),x).unwrap();
    assert!(rational.is_one());
    assert_eq!(rational.exclusions().len(),1);
    assert!(matches!(rational.evaluate(&[S::zero()]),Err(KernelError::DomainSingularity(_))));
    assert_eq!(rational.evaluate(&[S::from_i64(3)]).unwrap(),S::one());
}

#[test]
fn zero_numerator_does_not_remove_original_pole(){
    let x=v(1,0);
    let zero=Polynomial::zero(1);
    let rational=RationalFunction::new(zero,x).unwrap();
    assert!(rational.is_zero());
    assert!(matches!(rational.evaluate(&[S::zero()]),Err(KernelError::DomainSingularity(_))));
}

#[test]
fn polynomial_fraction_coefficient_normalizes_without_gcd(){
    let n=7;
    let x=v(n,0);
    let two=Polynomial::constant(n,S::from_i64(2));
    let half=RationalFunction::new(x.clone(),two).unwrap();
    assert!(half.denominator().is_one());
    assert_eq!(half.evaluate(&vec![S::from_i64(4);n]).unwrap(),S::from_i64(2));
}
