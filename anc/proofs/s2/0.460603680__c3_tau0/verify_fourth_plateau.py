"""Exact arithmetic and verifier for a fourth-plateau certificate, if found."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
import json
from pathlib import Path
from fractions import Fraction as Q
from algebraic_field import make_field
from verify_second_plateau import verify_exact

HERE=Path(__file__).resolve().parent
F=make_field([-22018716,1852200,-29356,0,1],root_interval=(127,128),local_isolation=True)
s=F([0,1,0,0])
sqrt7=(s*s-4472)/(54*s-2450)
assert sqrt7>0 and sqrt7*sqrt7==7
beta=(-20+14*sqrt7)/81
k=1-beta
D=s/27-sqrt7
assert D>0 and D*D==1-3*k+9*k*k
B=F(Q(2,3))*(D-3*k+1)
scale=(1+3*k-D)/(3*k)
a=(sqrt7-1)/3;b=(1-a)/3
assert a>0 and b>0 and a+3*b==1
assert 3*a*a*b+6*a*b*b==beta
PRIMITIVE=B


def check(cover,cert):
    endpoint=make_field([-4,0,0,1]);c=endpoint([0,1,0])
    cuts=([2/c,c] if len(cover['cuts'])==2 else
          [(c+2)/(2*c),2/c,(c+2)/(c*c),(c*c+c+2)/(c**3),c])
    if len(cover['cuts'])==3:
        templates=[sorted([2/c,q,c]) for q in
                   ((c+2)/(2*c),(c+2)/(c*c),(c*c+c+2)/4)]
        actual=[endpoint(q) for q in cover['cuts']]
        matches=[candidate for candidate in templates if candidate==actual]
        assert len(matches)==1,'Unexpected three-cut tau0 cover'
        cuts=matches[0]
    if len(cover['cuts'])==6:
        cuts.append((c*c+c+2)/(c*(c+2)))
    return verify_exact(cover,cert,field=F,bound=B,scale=scale,beta=beta,
        endpoint=(-4,0,0,1),expected_c=('0','1','0'),
        expected_cuts=tuple(tuple(q.json()) for q in sorted(cuts)),
        minimum_margin=Q(0))


if __name__=='__main__':
    cover=json.loads((HERE/'near_tau0_refined_cover.json').read_text())
    cert=json.loads((HERE/'fourth_plateau_exact_certificate.json').read_text())
    result=check(cover,cert)
    (HERE/'fourth_plateau_exact_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
