//! Exact Bareiss determinant, rational LDLᵀ and matrix operations.
use crate::kernel::{KernelError,KernelResult};
use crate::kernel::rational::ExactScalar as S;

fn check_square(matrix:&[Vec<S>])->KernelResult<usize>{
    let n=matrix.len();
    if n==0 || n>256 || matrix.iter().any(|r|r.len()!=n){
        return Err(KernelError::DimensionMismatch("matriz quadrada de ordem 1..256".into()));
    }
    Ok(n)
}
pub fn bareiss_determinant(matrix:&[Vec<S>])->KernelResult<S>{
    let n=check_square(matrix)?;
    let mut a=matrix.to_vec();
    let mut sign=S::one();let mut prev=S::one();
    for k in 0..n-1 {
        if a[k][k].is_zero(){
            match (k+1..n).find(|&i| !a[i][k].is_zero()){
                Some(i)=>{a.swap(i,k);sign=sign.negate();},
                None=>return Ok(S::zero()),
            }
        }
        let pivot=a[k][k].clone();
        for i in k+1..n{for j in k+1..n{
            a[i][j]=a[i][j].mul(&pivot).sub(&a[i][k].mul(&a[k][j])).div(&prev)?;
        }}
        for row in a.iter_mut().skip(k+1){row[k]=S::zero();}
        prev=pivot;
    }
    Ok(sign.mul(&a[n-1][n-1]))
}
#[derive(Clone,Debug)]
pub struct LdltCertificate{pub lower:Vec<Vec<S>>,pub diagonal:Vec<S>}
pub fn positive_definite_ldlt(gram:&[Vec<S>])->KernelResult<LdltCertificate>{
    let n=check_square(gram)?;
    if (0..n).any(|i|(0..n).any(|j|gram[i][j]!=gram[j][i])) {
        return Err(KernelError::InvalidCertificate("métrica não simétrica".into()));
    }
    let mut l=vec![vec![S::zero();n];n];let mut d=vec![S::zero();n];
    for i in 0..n{
        l[i][i]=S::one();
        let mut di=gram[i][i].clone();
        for k in 0..i{di=di.sub(&l[i][k].mul(&l[i][k]).mul(&d[k]));}
        if !di.is_positive(){return Err(KernelError::InvalidCertificate(format!("pivô LDLᵀ {i} = {di} não positivo")));}
        d[i]=di.clone();
        for j in i+1..n{
            let mut a=gram[j][i].clone();
            for k in 0..i{a=a.sub(&l[j][k].mul(&l[i][k]).mul(&d[k]));}
            l[j][i]=a.div(&di)?;
        }
    }
    // Check reconstruction exactly. Do not rely on unchecked factorization.
    for i in 0..n{for j in 0..n{
        let mut v=S::zero();
        for k in 0..n{v=v.add(&l[i][k].mul(&d[k]).mul(&l[j][k]));}
        if v!=gram[i][j]{return Err(KernelError::InvalidCertificate("reconstrução LDLᵀ".into()));}
    }}
    Ok(LdltCertificate{lower:l,diagonal:d})
}
pub fn rank(matrix:&[Vec<S>])->KernelResult<usize>{
    if matrix.is_empty(){return Ok(0);}
    let width=matrix[0].len();
    if matrix.iter().any(|r|r.len()!=width){return Err(KernelError::DimensionMismatch("matriz não retangular".into()));}
    let mut a=matrix.to_vec();let mut r=0;
    for c in 0..width{
        let pivot=(r..a.len()).find(|&i|!a[i][c].is_zero());
        if let Some(i)=pivot{
            a.swap(i,r);let p=a[r][c].clone();
            for j in c..width{a[r][j]=a[r][j].div(&p)?;}
            for i in r+1..a.len(){let f=a[i][c].clone();
                for j in c..width{a[i][j]=a[i][j].sub(&f.mul(&a[r][j]));}
            }
            r+=1;
            if r==a.len(){break;}
        }
    }
    Ok(r)
}
