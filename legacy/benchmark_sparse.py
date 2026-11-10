"""Reproducible sparse-kernel scaling, NOT a full invariant-mining benchmark.

Columns correspond to every monomial of total degree <= d in 12 variables,
including the constant. Synthetic adjacent-column constraints have known rank
n-1 and kernel span(1,...,1), allowing independent validation at both scales.
"""
import json
from math import comb
from time import perf_counter
import tracemalloc
from ml_mathlib_exact import SparseExactKernel


def run(degree):
    columns=comb(12+degree,degree)
    tracemalloc.start()
    start=perf_counter()
    solver=SparseExactKernel(columns,max_nonzeros=2*columns)
    for i in range(columns-1):
        solver.add_equation({i:1,i+1:-1})
    basis=solver.basis(max_basis=1)
    if (solver.rank!=columns-1 or len(basis)!=1
            or len(basis[0])!=columns or any(v!=1 for v in basis[0])):
        raise ArithmeticError('Synthetic sparse kernel failed independent check')
    elapsed=perf_counter()-start
    _,peak=tracemalloc.get_traced_memory()
    tracemalloc.stop()
    return dict(variables=12,maximum_degree=degree,monomials_including_constant=columns,
                equations=columns-1,rank=solver.rank,nullity=1,verified=True,
                seconds=elapsed,peak_traced_bytes=peak,coefficient_bits=1,
                workload='synthetic adjacent-column constraints; not invariant mining')


if __name__=='__main__':
    print(json.dumps([run(4),run(6)],indent=2))
