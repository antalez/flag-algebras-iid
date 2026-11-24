"""Standard-library exact verification for the plateau (phi,alpha1]."""

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
from verify_second_plateau import verify_exact

HERE=Path(__file__).resolve().parent
F=make_field([-6336,8640,-816,0,1],root_interval=(19,20),local_isolation=True)
s=F([0,1,0,0]);sqrt3=(s*s-192)/(12*s-120)
assert sqrt3>0 and sqrt3*sqrt3==3
beta=2*sqrt3/9;k=1-beta;D=s/6-sqrt3
assert D>0 and D*D==1-3*k+9*k*k
B=F(Q(2,3))*(D-3*k+1);scale=(1+3*k-D)/(3*k)
a=1-sqrt3/3;b=sqrt3/3
assert a>0 and b>0 and a+b==1 and a*a*b+2*a*b*b==beta


def check(cover,cert):
    return verify_exact(cover,cert,field=F,bound=B,scale=scale,beta=beta,
        endpoint=(-2,0,-1,1),expected_c=('0','1','0'),
        expected_cuts=(('0','-1','1'),('0','0','1/2'),('0','1','0')),
        minimum_margin=Q(19,250))


if __name__=='__main__':
    cover=json.loads((HERE/'near_alpha1_exact_cover.json').read_text())
    cert=json.loads((HERE/'alpha1_plateau_exact_certificate.json').read_text())
    result=check(cover,cert)
    (HERE/'alpha1_plateau_exact_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
