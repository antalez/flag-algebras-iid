"""Exact algebraic lower law on (alpha3,beta3prime]; no upper proof."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from fractions import Fraction as Q
from quadratic_tower import make_tower,extend_positive

T=make_tower(7,Q(121,27),Q(-28,27))
u=T([0,1,0,0]);v=T([0,0,1,0]);gamma=(-20+14*u)/81
assert v>0 and v*v==3-6*gamma
s=(3-v)/(3*(1+gamma))
a=s*(u-1)/3;b=s*(4-u)/9;h=1-s
assert min(a,b,h)>0 and a+3*b+h==1
assert 3*a*a*b+6*a*b*b==gamma*s**3
beta=h-h**3+gamma*s**3;k=1-beta
F=extend_positive(T,1-3*k+9*k*k)
k=F(k);D=F([0,0,0,0,1,0,0,0])
assert D>0 and D*D==1-3*k+9*k*k
w=(1+3*k-D)/(3*k);B=Q(2,3)*(D-3*k+1)
assert 0<w<1 and (1-k*w*w)/(3-3*w+w*w)==B
assert Q(50905413288916,10**14)<B<Q(50905413288917,10**14)
print('Exact uniform lower target lies in (0.50905413288916, 0.50905413288917)')
