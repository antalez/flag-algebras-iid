"""Exact arithmetic and signs in Q(t), t=positive cube_root(4)."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from fractions import Fraction as Q
from functools import lru_cache

def as_tuple(x):
    if isinstance(x,F):return x.v
    if isinstance(x,(list,tuple)):
        assert len(x)==3
        return tuple(map(Q,x))
    return (Q(x),Q(0),Q(0))

class F:
    __slots__=('v',)
    def __init__(self,x=0):self.v=as_tuple(x)
    def __add__(self,other):return F(tuple(a+b for a,b in zip(self.v,as_tuple(other))))
    __radd__=__add__
    def __neg__(self):return F(tuple(-a for a in self.v))
    def __sub__(self,other):return self+-F(other)
    def __rsub__(self,other):return F(other)+-self
    def __mul__(self,other):
        b=as_tuple(other);out=[Q(0)]*5
        for i in range(3):
            for j in range(3):out[i+j]+=self.v[i]*b[j]
        out[0]+=4*out[3];out[1]+=4*out[4]
        return F(tuple(out[:3]))
    __rmul__=__mul__
    def __truediv__(self,other):return self*F(inverse(as_tuple(other)))
    def __rtruediv__(self,other):return F(other)/self
    def __bool__(self):return any(self.v)
    def __hash__(self):return hash(self.v)
    def __eq__(self,other):return self.v==as_tuple(other)
    def __lt__(self,other):return sign((self-F(other)).v)<0
    def __le__(self,other):return sign((self-F(other)).v)<=0
    def __gt__(self,other):return sign((self-F(other)).v)>0
    def __ge__(self,other):return sign((self-F(other)).v)>=0
    def __float__(self):
        t=4**(1/3)
        return sum(float(v)*t**i for i,v in enumerate(self.v))
    def json(self):return list(map(str,self.v))

@lru_cache(None)
def inverse(v):
    assert any(v)
    columns=[(F(v)*F(tuple(Q(i==j) for i in range(3)))).v for j in range(3)]
    a=[[columns[j][i] for j in range(3)]+[Q(i==0)] for i in range(3)]
    for j in range(3):
        k=next(k for k in range(j,3) if a[k][j]);a[k],a[j]=a[j],a[k]
        pivot=a[j][j];a[j]=[x/pivot for x in a[j]]
        for i in range(3):
            if i!=j:
                scale=a[i][j];a[i]=[x-scale*y for x,y in zip(a[i],a[j])]
    return tuple(a[i][-1] for i in range(3))

@lru_cache(None)
def interval(bits):
    den=1<<bits;lo=den;hi=2*den
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**3<4*den**3:lo=mid
        else:hi=mid
    assert lo**3<4*den**3<hi**3
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
    raise ArithmeticError('Increase root-isolation precision')

def solve(matrix,rhs,free=None):
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
