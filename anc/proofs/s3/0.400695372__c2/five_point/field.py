"""Standard-library exact arithmetic in Q(r), r^4-4r^3-3r^2-2r+2=0, 0<r<1.

The defining polynomial decreases strictly on (0,1), with opposite endpoint
signs, so this interval specifies one root. Signs use rational isolation only.
"""
from fractions import Fraction as Q
from functools import lru_cache
POLY=(2,-2,-3,-4,1)
@lru_cache(None)
def interval(bits):
    den=1<<bits;lo=0;hi=den
    def p(v):return sum(a*v**i*den**(4-i) for i,a in enumerate(POLY))
    while hi-lo>1:
        m=(lo+hi)//2
        if p(m)>0:lo=m
        else:hi=m
    assert p(lo)>0>p(hi)
    return Q(lo,den),Q(hi,den)
@lru_cache(None)
def sign(v):
    if not any(v):return 0
    for bits in (80,160,320,640,1280,2560):
        lo,hi=interval(bits)
        low=v[0]+sum(a*(lo**i if a>=0 else hi**i) for i,a in enumerate(v[1:],1))
        high=v[0]+sum(a*(hi**i if a>=0 else lo**i) for i,a in enumerate(v[1:],1))
        if low>0:return 1
        if high<0:return -1
    raise ArithmeticError('Unresolved sign; refuse certificate')
class F:
    __slots__=('v',)
    def __init__(self,x=0):
        if isinstance(x,F):self.v=x.v
        elif isinstance(x,(list,tuple)):
            assert len(x)<=4;self.v=tuple(map(Q,x))+(Q(0),)*(4-len(x))
        else:self.v=(Q(x),Q(0),Q(0),Q(0))
    def __add__(self,b):return F([a+c for a,c in zip(self.v,F(b).v)])
    __radd__=__add__
    def __neg__(self):return F([-a for a in self.v])
    def __sub__(self,b):return self+-F(b)
    def __rsub__(self,b):return F(b)+-self
    def __mul__(self,b):
        b=F(b).v;out=[Q(0)]*7
        for i,a in enumerate(self.v):
            if a:
                for j,c in enumerate(b):
                    if c:out[i+j]+=a*c
        for i in (6,5,4):
            if out[i]:
                for j in range(4):out[i-4+j]-=out[i]*POLY[j]
        return F(out[:4])
    __rmul__=__mul__
    def __truediv__(self,b):
        b=F(b)
        if not any(b.v[1:]):return F([a/b.v[0] for a in self.v])
        return self*F(inverse(b.v))
    def __rtruediv__(self,b):return F(b)/self
    def __pow__(self,n):
        if n<0:return (1/self)**(-n)
        out=F(1);base=self
        while n:
            if n%2:out=out*base
            base=base*base;n//=2
        return out
    def __bool__(self):return any(self.v)
    def __eq__(self,b):return self.v==F(b).v
    def __lt__(self,b):return sign((self-F(b)).v)<0
    def __le__(self,b):return sign((self-F(b)).v)<=0
    def __gt__(self,b):return sign((self-F(b)).v)>0
    def __ge__(self,b):return sign((self-F(b)).v)>=0
    def __float__(self):
        lo,hi=interval(80);r=float((lo+hi)/2)
        return sum(float(a)*r**i for i,a in enumerate(self.v))
    def json(self):return list(map(str,self.v))
@lru_cache(None)
def inverse(v):
    assert any(v)
    cols=[(F(v)*F([int(i==j) for i in range(4)])).v for j in range(4)]
    a=[[cols[j][i] for j in range(4)]+[Q(i==0)] for i in range(4)]
    for j in range(4):
        k=next(k for k in range(j,4) if a[k][j]);a[j],a[k]=a[k],a[j];d=a[j][j];a[j]=[x/d for x in a[j]]
        for i in range(4):
            if i!=j and a[i][j]:
                d=a[i][j];a[i]=[x-d*y for x,y in zip(a[i],a[j])]
    return tuple(a[i][-1] for i in range(4))

def positive_definite(matrix):
    a=[[F(v) for v in row] for row in matrix];n=len(a)
    assert n and all(len(row)==n for row in a)
    assert all(a[i][j]==a[j][i] for i in range(n) for j in range(n))
    for k in range(n):
        assert a[k][k]>0,('nonpositive LDL pivot',k,float(a[k][k]))
        for i in range(k+1,n):
            t=a[i][k]/a[k][k]
            for j in range(i,n):a[j][i]=a[i][j]=a[i][j]-t*a[k][j]
    return True
R=F([0,1]);BSTAR=R*(2-R)/(1+R+R**2+R**3)
