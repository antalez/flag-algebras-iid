"""Verifier scaffold for an exact (alpha1,alpha2] certificate, if found.

Arithmetic uses u^2=19, v^2=(4017835-400026*u)/923521, u,v>0.
No exact alpha2 certificate is claimed until every check below passes.
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
from quadratic_tower import make_tower
from algebraic_field import make_field
from verify_second_plateau import verify_exact

HERE=Path(__file__).resolve().parent
F=make_tower(19,Q(4017835,923521),Q(-400026,923521))
u=F([0,1,0,0]);D=F([0,0,1,0])
beta=(216+38*u)/961;k=1-beta
assert D*D==1-3*k+9*k*k
B=F(Q(2,3))*(D-3*k+1);scale=(1+3*k-D)/(3*k)
s=(27-3*u)/31;a=2*s/3;b=s/3;h=1-s
assert min(a,b,h)>0 and a+b+h==1
assert a*a*b+h-h**3==beta


def check(cover,cert):
    endpoint_field=make_field([-2,-1,0,-1,1])
    c=endpoint_field([0,1,0,0])
    cuts=[2/c,1/(c-1),2/(c*(c-1)),c]
    if len(cover['cuts'])==6:cuts.extend([(c+2)/(2*c),(c+2)/(c*c)])
    expected=tuple(tuple(q.json()) for q in sorted(cuts))
    return verify_exact(cover,cert,field=F,bound=B,scale=scale,beta=beta,
        endpoint=(-2,-1,0,-1,1),expected_c=('0','1','0','0'),
        expected_cuts=expected,
        minimum_margin=Q(1,250))


if __name__=='__main__':
    cover=json.loads((HERE/'near_alpha2_refined_cover.json').read_text())
    cert=json.loads((HERE/'alpha2_plateau_exact_certificate.json').read_text())
    result=check(cover,cert)
    (HERE/'alpha2_plateau_exact_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
