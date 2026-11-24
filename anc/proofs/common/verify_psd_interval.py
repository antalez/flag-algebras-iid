"""Prove positive definiteness using exact enclosures and integer arithmetic.

Floating-point Cholesky supplies only a candidate change of basis. Every
entry enclosure and the final strict diagonal-dominance test are exact.

If M is the integer midpoint matrix and |grid*Y-M|<=1 entrywise, put
H=R*M*R^T and r_i=sum_k |R_ik| for the proposed integer matrix R. Then
|(R*(grid*Y-M)*R^T)_ij|<=r_i*r_j. The tested inequality
H_ii>sum_{j!=i}|H_ij|+r_i*sum_j r_j proves R*Y*R^T is strictly
diagonally dominant with positive diagonal. It is therefore positive
definite, which also forces square R to be invertible and proves Y>0.
"""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from fractions import Fraction
from math import isfinite, sqrt


def positive_definite_interval(matrix, grid=10**8, transform_scale=10**6):
    n=len(matrix)
    assert n and all(len(row)==n for row in matrix)
    assert all(matrix[i][j]==matrix[j][i] for i in range(n) for j in range(i))
    mids=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1):
            x=matrix[i][j]
            value=float(x)
            assert isfinite(value)
            midpoint=round(grid*value)
            assert Fraction(midpoint-1,grid)<=x<=Fraction(midpoint+1,grid)
            mids[i][j]=mids[j][i]=midpoint

    # A numerical inverse Cholesky factor only proposes the congruence.
    lower=[[0.0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1):
            z=mids[i][j]/grid-sum(lower[i][k]*lower[j][k] for k in range(j))
            lower[i][j]=sqrt(z) if i==j else z/lower[j][j]
    inverse=[[0.0]*n for _ in range(n)]
    for i in range(n):
        inverse[i][i]=1/lower[i][i]
        for j in range(i):
            inverse[i][j]=-sum(lower[i][k]*inverse[k][j] for k in range(j,i))/lower[i][i]
    R=[[round(transform_scale*x) for x in row] for row in inverse]
    norms=[sum(abs(x) for x in row) for row in R]
    RM=[[sum(R[i][k]*mids[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
    H=[[sum(RM[i][k]*R[j][k] for k in range(n)) for j in range(n)] for i in range(n)]
    for i in range(n):
        error=norms[i]*sum(norms)
        assert H[i][i]>sum(abs(H[i][j]) for j in range(n) if j!=i)+error
