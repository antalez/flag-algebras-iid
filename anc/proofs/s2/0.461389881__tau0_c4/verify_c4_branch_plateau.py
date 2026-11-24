"""Exact verification scaffold for a possible plateau on (tau0,c4].

The one-scale law and its boost are checked exactly, but a matching upper
certificate is not yet known.  The first generator is twice the smallest
atom's mass, isolated as the unique root in (1,2) of the polynomial below.
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
T = make_field([-2304, 7040, -576, -11136, 2952, 3753], local_isolation=True)
a0 = T([0, 1, 0, 0, 0])/2
b0 = -(28841805*a0**5+19225611*a0**4-16124046*a0**3-4953896*a0**2+2011200*a0)/(16514*a0)
t0 = (37833993*a0**5+25282872*a0**4-21120918*a0**3-6549752*a0**2+2655736*a0)/(33028*a0)
d0 = 1-a0-b0-t0
assert min(a0,b0,t0,d0) > 0 and a0+b0+t0+d0 == 1
beta0 = a0*a0*(b0+t0+d0)+2*a0*b0*(t0+d0)+2*a0*t0*d0+b0*b0*d0
k0 = 1-beta0
F = extend_positive(T, 1-3*k0+9*k0*k0)
a = F(a0); beta = F(beta0); k = 1-beta
D = F([0]*5+[1]+[0]*4)
assert D > 0 and D*D == 1-3*k+9*k*k
B = Q(2,3)*(D-3*k+1)
scale = (1+3*k-D)/(3*k)
assert 0 < scale < 1
assert (1-k*scale*scale)/(3-3*scale+scale*scale) == B
assert Q(4613898814527,10**13) < B < Q(4613898814528,10**13)
PRIMITIVE = a+D


def check(cover,cert):
    endpoint = make_field([-2,-1,-1,-1,0,1])
    c = endpoint([0,1,0,0,0])
    cuts = sorted([2/c,c,(c+2)/(c*c),(c+2)/(2*c),
                   (c*c+c+2)/(c**3),4/(c*c)])
    return verify_exact(cover,cert,field=F,bound=B,scale=scale,beta=beta,
        endpoint=(-2,-1,-1,-1,0,1),expected_c=('0','1','0','0','0'),
        expected_cuts=tuple(tuple(q.json()) for q in cuts),minimum_margin=Q(0))


if __name__ == '__main__':
    cover = json.loads((HERE/'near_c4_branch_refined_cover.json').read_text())
    cert = json.loads((HERE/'c4_branch_plateau_exact_certificate.json').read_text())
    result = check(cover,cert)
    (HERE/'c4_branch_plateau_exact_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
