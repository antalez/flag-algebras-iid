"""Verify a narrow uniform band on the candidate plateau (alpha3,alpha4]."""

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
from verify_near_small import verify_near
from verify_alpha4_plateau import B

HERE=Path(__file__).resolve().parent


def check():
    cover=json.loads((HERE/'near_alpha4_exact_cover.json').read_text())
    cert=json.loads((HERE/'near_alpha4_certificate.json').read_text())
    polynomial=[-2,-1,-1,-1,0,-1,1]
    assert cover['n']==4 and cover['polynomial']==polynomial
    endpoint=make_field(polynomial);c=endpoint([0,1,0,0,0,0])
    assert cover['c']==c.json()
    assert c**5-c**4-c**2-c-2>0
    result=verify_near(cover,cert)
    upper=Q(result['upper'])
    lower=Q('0.50905413288916')
    width=Q('0.000000233')
    assert lower<B<upper and upper-lower<width
    # The lower construction is uniform for c>alpha3; monotonicity extends
    # this exact endpoint upper to every c<=alpha4.
    return dict(interval='(alpha3,alpha4]',lower_algebraic=B.json(),
                lower_rounded_down=str(lower),upper=str(upper),
                upper_decimal=float(upper),maximum_interval_variation=str(width),
                exact_plateau_proved=False,all_exact_checks_passed=True)


if __name__=='__main__':
    result=check()
    (HERE/'alpha4_plateau_band.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
