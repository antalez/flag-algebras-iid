"""Exact uniform right-hand lower construction at the alpha4 threshold."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from fractions import Fraction as Q
from quadratic_tower import make_tower,extend_positive

T=make_tower(13,Q(62,9),Q(-13,9))
u=T([0,1,0,0]);v=T([0,0,1,0]);gamma=(-35+13*u)/54
assert v>0 and v*v==3-6*gamma
s=(3-v)/(3*(1+gamma));a=s*(u-2)/3;b=s*(5-u)/12;h=1-s
assert min(a,b,h)>0 and a+4*b+h==1
assert 4*a*a*b+12*a*b*b==gamma*s**3
beta=h-h**3+gamma*s**3;k=1-beta
F=extend_positive(T,1-3*k+9*k*k);k=F(k)
D=F([0,0,0,0,1,0,0,0])
assert D>0 and D*D==1-3*k+9*k*k
w=(1+3*k-D)/(3*k);B=Q(2,3)*(D-3*k+1)
assert 0<w<1 and (1-k*w*w)/(3-3*w+w*w)==B
assert Q(5093764319755,10**13)<B<Q(5093764319756,10**13)
if __name__ == '__main__':
    print('Uniform right lower bound in (0.5093764319755, 0.5093764319756)')
