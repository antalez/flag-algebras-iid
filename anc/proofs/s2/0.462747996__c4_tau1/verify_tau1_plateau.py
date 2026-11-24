"""Exact lower-law identities and upper-certificate scaffold on (c4,tau1].

A matching upper certificate is still needed to prove a plateau.
"""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
import json
from fractions import Fraction as Q
from pathlib import Path
from algebraic_field import make_field
from quadratic_tower import extend_positive
from verify_second_plateau import verify_exact

HERE = Path(__file__).resolve().parent
T = make_field([-1024,-13312,52096,-30208,-43392,24984,9909],
               local_isolation=True)
a0 = T([0,1,0,0,0,0])/2
b0 = (-2412811773*a0**5- Q(15054167457,4)*a0**4
      +1515999129*a0**3+1373405291*a0**2-382391573*a0-13082260)/226049
t0 = (Q(3815787447,4)*a0**5+1488346830*a0**4
      -Q(2394801321,4)*a0**3-543088296*a0**2+150821999*a0+5297225)/226049
d0 = 1-a0-b0-2*t0
assert min(a0,b0,t0,d0)>0 and a0+b0+2*t0+d0==1
# These are the three partial derivatives after eliminating d=1-a-b-2t.
assert (-3*a0*a0-4*a0*b0-8*a0*t0+2*a0-3*b0*b0
        -4*b0*t0+2*b0-6*t0*t0+4*t0)==0
assert -2*a0*a0-6*a0*b0-4*a0*t0+2*a0-3*b0*b0-4*b0*t0+2*b0==0
assert -4*a0*a0-4*a0*b0-12*a0*t0+4*a0-2*b0*b0==0
beta0 = a0*a0*(1-a0)+2*a0*b0*(2*t0+d0)+2*a0*t0*(t0+2*d0)+b0*b0*d0
k0 = 1-beta0
F = extend_positive(T,1-3*k0+9*k0*k0)
a,b,t,d = map(F,(a0,b0,t0,d0))
assert b*(a-d)==a*t and d-t==b*b/(2*a)
beta=F(beta0);k=1-beta
D=F([0]*6+[1]+[0]*5)
assert D>0 and D*D==1-3*k+9*k*k
scale=(1+3*k-D)/(3*k)
B=Q(2,3)*(D-3*k+1)
assert 0<scale<1 and (1-k*scale*scale)/(3-3*scale+scale*scale)==B
assert Q(46274799646310,10**14)<B<Q(46274799646312,10**14)
PRIMITIVE=B
# At c4 the fourth ladder atom meets the upper endpoint. The additional
# success 2*x1<c*x4 is already strict there, so it persists just to the right.
E=make_field([-2,-1,-1,-1,0,1]);c4=E([0,1,0,0,0])
r1=2/c4;r2=(1+r1)/c4;r3=(1+r2)/c4;r4=(1+r3)/c4
assert 1<r1<r2<r3<r4 and r4==c4 and 2*r1<c4*r4


def check(cover,cert):
    endpoint=make_field([-4,0,-1,0,1])
    c=endpoint([0,1,0,0])
    r1=2/c;r2=(1+r1)/c;r3=(1+r2)/c;r4=(1+r3)/c
    cuts=sorted([r1,r2,r3,r4,c,r2/r1])
    return verify_exact(cover,cert,field=F,bound=B,scale=scale,beta=beta,
        endpoint=(-4,0,-1,0,1),expected_c=('0','1','0','0'),
        expected_cuts=tuple(tuple(q.json()) for q in cuts),minimum_margin=Q(1,1000))


if __name__=='__main__':
    print('Exact lower target lies in (0.46274799646310, 0.46274799646312)')
    path=HERE/'tau1_plateau_exact_certificate.json'
    if path.exists():
        cover=json.loads((HERE/'near_tau1_refined_cover.json').read_text())
        result=check(cover,json.loads(path.read_text()))
        (HERE/'tau1_plateau_exact_verification.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result,indent=2))
