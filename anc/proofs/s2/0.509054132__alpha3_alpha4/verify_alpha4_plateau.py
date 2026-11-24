"""Exact verifier for the candidate plateau (alpha3,alpha4]."""

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
from quadratic_tower import make_tower, extend_positive
from verify_second_plateau import verify_exact
from verify_psd_interval import positive_definite_interval

HERE = Path(__file__).resolve().parent
T = make_tower(7, Q(121,27), Q(-28,27))
u0 = T([0,1,0,0]); v0 = T([0,0,1,0])
gamma0 = (-20+14*u0)/81
s0 = (3-v0)/(3*(1+gamma0))
beta0 = 2*s0-3*s0*s0+(1+gamma0)*s0**3
k0 = 1-beta0
F = extend_positive(T, 1-3*k0+9*k0*k0)
u = F(u0); v = F(v0); D = F([0,0,0,0,1,0,0,0])
gamma = (-20+14*u)/81
s = (3-v)/(3*(1+gamma))
beta = 2*s-3*s*s+(1+gamma)*s**3; k = 1-beta
assert D > 0 and D*D == 1-3*k+9*k*k
B = Q(2,3)*(D-3*k+1)
scale = (1+3*k-D)/(3*k)
a = s*(u-1)/3; b = s*(4-u)/9; h = 1-s
assert min(a,b,h) > 0 and a+3*b+h == 1
assert 3*a*a*b+6*a*b*b == gamma*s**3
assert h-h**3+gamma*s**3 == beta
assert 0 < scale < 1 and (1-k*scale**2)/(3-3*scale+scale**2) == B
assert Q(50905413288916,10**14) < B < Q(50905413288917,10**14)
PRIMITIVE = B


def check(cover, cert):
    polynomial = [-2,-1,-1,-1,0,-1,1]
    endpoint = make_field(polynomial); c = endpoint([0,1,0,0,0,0])
    cuts = sorted([2/c,c,1/(c-1),(c+2)/(2*c),(c+2)/(c*c),
                   (c*c+c+2)/(c**3)])
    return verify_exact(cover, cert, field=F, bound=B, scale=scale, beta=beta,
        endpoint=tuple(polynomial), expected_c=('0','1','0','0','0','0'),
        expected_cuts=tuple(tuple(q.json()) for q in cuts),
        minimum_margin=Q(1,250), psd_check=positive_definite_interval)


if __name__ == '__main__':
    cover = json.loads((HERE/'near_alpha4_exact_cover.json').read_text())
    cert = json.loads((HERE/'alpha4_plateau_exact_certificate.json').read_text())
    result = check(cover, cert)
    (HERE/'alpha4_plateau_exact_verification.json').write_text(
        json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
