"""Exact root arithmetic for polynomials with an isolated root in (1,2).

No numerical approximations are used for signs. A failed inverse or unresolved
zero raises an error rather than accepting a proof. Intended moduli are the
irreducible endpoint polynomials recorded with each certificate.
"""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from fractions import Fraction as Q
from functools import lru_cache
from math import comb

def make_field(polynomial,root_interval=(1,2),local_isolation=False):
    polynomial=tuple(polynomial);degree=len(polynomial)-1
    assert degree>=2 and polynomial[-1]>0
    assert all(type(v)==int for v in polynomial)
    nonzero=[v for v in polynomial if v]
    if not local_isolation:
        assert polynomial[0]<0
        assert sum(a*b<0 for a,b in zip(nonzero,nonzero[1:]))==1
    left,right=root_interval
    assert 0<left<right and all(type(v)==int for v in root_interval)
    if local_isolation:
        coarse=sum(j*v*(left**(j-1) if v>=0 else right**(j-1))
                   for j,v in enumerate(polynomial) if j)>0
        # Positive coefficients of p'(left + y) prove strict increase for
        # every y >= 0, and can be much sharper than the coarse bound.
        shifted=[sum(j*polynomial[j]*comb(j-1,k)*left**(j-1-k)
                     for j in range(k+1,degree+1)) for k in range(degree)]
        assert coarse or (shifted[0]>0 and all(v>=0 for v in shifted))
    assert sum(v*left**j for j,v in enumerate(polynomial))<0<sum(v*right**j for j,v in enumerate(polynomial))
    leading=polynomial[-1]
    if leading != 1:
        polynomial=tuple(Q(v,leading) for v in polynomial)

    @lru_cache(None)
    def interval(bits):
        den=1<<bits;lo=left*den;hi=right*den
        def value(x):return sum(v*x**j*den**(degree-j) for j,v in enumerate(polynomial))
        while hi-lo>1:
            mid=(lo+hi)//2
            if value(mid)<0:lo=mid
            else:hi=mid
        assert value(lo)<0<value(hi)
        return Q(lo,den),Q(hi,den)

    @lru_cache(None)
    def sign(v):
        if not any(v):return 0
        for bits in [80,160,320,640,1280]:
            lo,hi=interval(bits)
            lower=v[0]+sum(a*(lo**i if a>=0 else hi**i) for i,a in enumerate(v[1:],1))
            upper=v[0]+sum(a*(hi**i if a>=0 else lo**i) for i,a in enumerate(v[1:],1))
            if lower>0:return 1
            if upper<0:return -1
        raise ArithmeticError('Unresolved algebraic sign; do not accept this proof')

    def coefficients(x):
        if isinstance(x,F):return x.v
        if isinstance(x,(list,tuple)):
            assert len(x)==degree
            return tuple(map(Q,x))
        return (Q(x),)+(Q(0),)*(degree-1)

    class F:
        __slots__=('v',)
        def __init__(self,x=0):self.v=coefficients(x)
        def __add__(self,other):return F(tuple(a+b for a,b in zip(self.v,coefficients(other))))
        __radd__=__add__
        def __neg__(self):return F(tuple(-a for a in self.v))
        def __sub__(self,other):return self+-F(other)
        def __rsub__(self,other):return F(other)+-self
        def __mul__(self,other):
            b=coefficients(other);out=[Q(0)]*(2*degree-1)
            for i in range(degree):
                if not self.v[i]:continue
                for j in range(degree):
                    if b[j]:out[i+j]+=self.v[i]*b[j]
            for i in range(len(out)-1,degree-1,-1):
                if not out[i]:continue
                for j in range(degree):
                    if polynomial[j]:out[i-degree+j]-=out[i]*polynomial[j]
            return F(tuple(out[:degree]))
        __rmul__=__mul__
        def __truediv__(self,other):return self*F(inverse(coefficients(other)))
        def __rtruediv__(self,other):return F(other)/self
        def inverse(self):return F(inverse(self.v))
        def sign(self):return sign(self.v)
        def __pow__(self,n):
            assert type(n)==int
            if n<0:return (1/self)**(-n)
            result=F(1);base=self
            while n:
                if n%2:result=result*base
                base=base*base;n//=2
            return result
        def __bool__(self):return any(self.v)
        def __hash__(self):return hash(self.v)
        def __eq__(self,other):return self.v==coefficients(other)
        def __lt__(self,other):return sign((self-F(other)).v)<0
        def __le__(self,other):return sign((self-F(other)).v)<=0
        def __gt__(self,other):return sign((self-F(other)).v)>0
        def __ge__(self,other):return sign((self-F(other)).v)>=0
        def __float__(self):
            lo,hi=interval(64);t=float((lo+hi)/2)
            return sum(float(v)*t**i for i,v in enumerate(self.v))
        def json(self):return list(map(str,self.v))

    @lru_cache(None)
    def inverse(v):
        assert any(v)
        columns=[(F(v)*F(tuple(Q(i==j) for i in range(degree)))).v for j in range(degree)]
        a=[[columns[j][i] for j in range(degree)]+[Q(i==0)] for i in range(degree)]
        for j in range(degree):
            k=next(k for k in range(j,degree) if a[k][j]);a[k],a[j]=a[j],a[k]
            p=a[j][j];a[j]=[x/p for x in a[j]]
            for i in range(degree):
                if i!=j and a[i][j]:
                    p=a[i][j];a[i]=[x-p*y for x,y in zip(a[i],a[j])]
        return tuple(a[i][-1] for i in range(degree))

    return F

def solve(F,matrix,rhs,free=None):
    if not matrix:return None
    n=len(matrix[0]);a=[[F(v) for v in row]+[F(b)] for row,b in zip(matrix,rhs)]
    rank=0;pivots=[]
    for j in range(n):
        pivot=next((i for i in range(rank,len(a)) if a[i][j]),None)
        if pivot is None:continue
        a[rank],a[pivot]=a[pivot],a[rank]
        p=a[rank][j];a[rank]=[v/p for v in a[rank]]
        for i in range(len(a)):
            if i!=rank and a[i][j]:
                p=a[i][j];a[i]=[v-p*w for v,w in zip(a[i],a[rank])]
        pivots.append(j);rank+=1
    if any(not any(row[:-1]) and row[-1] for row in a):return None
    out=[F(v) for v in free] if free is not None else [F(0)]*n
    for i,j in reversed(list(enumerate(pivots))):out[j]=a[i][-1]-sum(a[i][k]*out[k] for k in range(j+1,n))
    return out
