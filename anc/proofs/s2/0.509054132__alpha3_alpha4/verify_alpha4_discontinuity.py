"""Verify the exact alpha4 upper certificate and its uniform right-hand jump."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
import json
from fractions import Fraction as Q
from math import floor
from pathlib import Path
from algebraic_field import make_field
from verify_near_small import verify_near
from check_alpha4_right_lower import B as RIGHT, F

HERE = Path(__file__).resolve().parent


def check():
    cover = json.loads((HERE/'near_alpha4_exact_cover.json').read_text())
    cert = json.loads((HERE/'near_alpha4_certificate.json').read_text())
    polynomial = [-2,-1,-1,-1,0,-1,1]
    assert cover['polynomial'] == polynomial
    endpoint = make_field(polynomial); c = endpoint([0,1,0,0,0,0])
    assert cover['n'] == 4 and cover['c'] == c.json()
    cuts = sorted([2/c,c,1/(c-1),(c+2)/(2*c),(c+2)/(c*c),
                   (c*c+c+2)/c**3])
    assert cover['cuts'] == [q.json() for q in cuts]
    assert Q('1.7463314890021') < c < Q('1.7463314890022')
    assert c**5-c**4-c**2-c-2 > 0
    assert c*(c-1)**2 < 1
    upper = verify_near(cover,cert)
    bound = Q(upper['upper'])
    jump = RIGHT-bound
    assert jump > 0
    denominator = 10**12
    numerator = floor(float(jump)*denominator)
    while Q(numerator,denominator) >= jump:
        numerator -= 1
    while Q(numerator+1,denominator) < jump:
        numerator += 1
    jump_lower = Q(numerator,denominator)
    assert jump_lower > 0 and RIGHT > bound+jump_lower
    return dict(endpoint_polynomial=polynomial,endpoint_decimal=float(c),
                patterns=upper['patterns'],upper=str(bound),upper_decimal=float(bound),
                uniform_right_lower=RIGHT.json(),uniform_right_lower_decimal=float(RIGHT),
                jump_lower=str(jump_lower),jump_lower_decimal=float(jump_lower),
                all_exact_checks_passed=True)


if __name__ == '__main__':
    result = check()
    (HERE/'alpha4_discontinuity.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
