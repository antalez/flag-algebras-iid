"""Exact ordered arithmetic in Q[u,v]/(u^2-d, v^2-p-q*u), u,v>0.

Signs use successive squaring, not floating point. Elements are stored in
the basis (1,u,v,u*v). Inversion rejects a zero norm.
"""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from fractions import Fraction as Q
from math import sqrt


def make_tower(d,p,q):
    d=Q(d);p=Q(p);q=Q(q)
    assert d>0
    def add(a,b):return (a[0]+b[0],a[1]+b[1])
    def neg(a):return (-a[0],-a[1])
    def mul(a,b):return (a[0]*b[0]+d*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
    def inv(a):
        norm=a[0]*a[0]-d*a[1]*a[1]
        assert norm
        return (a[0]/norm,-a[1]/norm)
    def signq(a):
        x,y=a
        if not x:return (y>0)-(y<0)
        if not y:return (x>0)-(x<0)
        sx=(x>0)-(x<0);sy=(y>0)-(y<0)
        if sx==sy:return sx
        diff=x*x-d*y*y
        return sx*((diff>0)-(diff<0))
    rad=(p,q)
    assert signq(rad)>0
    def coeff(x):
        if isinstance(x,F):return x.v
        if isinstance(x,(list,tuple)):
            assert len(x)==4
            return tuple(map(Q,x))
        return (Q(x),Q(0),Q(0),Q(0))
    class F:
        __slots__=('v',)
        def __init__(self,x=0):self.v=coeff(x)
        def __add__(self,x):return F(tuple(a+b for a,b in zip(self.v,coeff(x))))
        __radd__=__add__
        def __neg__(self):return F(tuple(-a for a in self.v))
        def __sub__(self,x):return self+-F(x)
        def __rsub__(self,x):return F(x)+-self
        def __mul__(self,x):
            other=coeff(x);a,b=self.v[:2],self.v[2:];c,e=other[:2],other[2:]
            return F(add(mul(a,c),mul(rad,mul(b,e)))+add(mul(a,e),mul(b,c)))
        __rmul__=__mul__
        def inverse(self):
            a,b=self.v[:2],self.v[2:]
            norm=add(mul(a,a),neg(mul(rad,mul(b,b))))
            ni=inv(norm)
            return F(mul(a,ni)+neg(mul(b,ni)))
        def __truediv__(self,x):return self*F(x).inverse()
        def __rtruediv__(self,x):return F(x)*self.inverse()
        def __pow__(self,n):
            assert isinstance(n,int)
            if n<0:return self.inverse()**(-n)
            out=F(1);a=self
            while n:
                if n%2:out*=a
                a*=a;n//=2
            return out
        def sign(self):
            a,b=self.v[:2],self.v[2:];sa=signq(a);sb=signq(b)
            if not sa:return sb
            if not sb:return sa
            if sa==sb:return sa
            diff=add(mul(a,a),neg(mul(rad,mul(b,b))))
            return sa*signq(diff)
        def __bool__(self):return any(self.v)
        def __eq__(self,x):return self.v==coeff(x)
        def __lt__(self,x):return (self-F(x)).sign()<0
        def __le__(self,x):return (self-F(x)).sign()<=0
        def __gt__(self,x):return (self-F(x)).sign()>0
        def __ge__(self,x):return (self-F(x)).sign()>=0
        def __hash__(self):return hash(self.v)
        def json(self):return list(map(str,self.v))
        def __float__(self):
            u=sqrt(float(d));v=sqrt(float(p)+float(q)*u)
            return float(self.v[0])+float(self.v[1])*u+float(self.v[2])*v+float(self.v[3])*u*v
    return F


def extend_positive(base,radicand):
    """Adjoin a positive square root to a finite-dimensional ordered field."""
    rad=base(radicand)
    assert rad>0
    degree=len(base(0).v)
    def coeff(x):
        if isinstance(x,F):return x.v
        if isinstance(x,base):return x.v+(Q(0),)*degree
        if isinstance(x,(tuple,list)):
            assert len(x)==2*degree
            return tuple(map(Q,x))
        return (Q(x),)+(Q(0),)*(2*degree-1)
    class F:
        __slots__=('v',)
        def __init__(self,x=0):self.v=coeff(x)
        def parts(self):return base(self.v[:degree]),base(self.v[degree:])
        def __add__(self,x):return F(tuple(a+b for a,b in zip(self.v,coeff(x))))
        __radd__=__add__
        def __neg__(self):return F(tuple(-a for a in self.v))
        def __sub__(self,x):return self+-F(x)
        def __rsub__(self,x):return F(x)+-self
        def __mul__(self,x):
            a,b=self.parts();c,e=F(x).parts()
            return F((a*c+rad*b*e).v+(a*e+b*c).v)
        __rmul__=__mul__
        def inverse(self):
            a,b=self.parts();inv=(a*a-rad*b*b).inverse()
            return F((a*inv).v+(-b*inv).v)
        def __truediv__(self,x):return self*F(x).inverse()
        def __rtruediv__(self,x):return F(x)*self.inverse()
        def __pow__(self,n):
            assert isinstance(n,int)
            if n<0:return self.inverse()**(-n)
            out=F(1);a=self
            while n:
                if n%2:out*=a
                a*=a;n//=2
            return out
        def sign(self):
            a,b=self.parts();sa=a.sign();sb=b.sign()
            if not sa:return sb
            if not sb:return sa
            if sa==sb:return sa
            return sa*(a*a-rad*b*b).sign()
        def __bool__(self):return any(self.v)
        def __eq__(self,x):return self.v==coeff(x)
        def __lt__(self,x):return (self-F(x)).sign()<0
        def __le__(self,x):return (self-F(x)).sign()<=0
        def __gt__(self,x):return (self-F(x)).sign()>0
        def __ge__(self,x):return (self-F(x)).sign()>=0
        def __hash__(self):return hash(self.v)
        def json(self):return list(map(str,self.v))
        def __float__(self):
            a,b=self.parts();return float(a)+float(b)*sqrt(float(rad))
    return F
