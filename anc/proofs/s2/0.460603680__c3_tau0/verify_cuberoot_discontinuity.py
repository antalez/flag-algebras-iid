"""Combined exact check of the new cube-root discontinuity. Standard library only.

The uniform lower-family feasibility is proved explicitly in graph_certificates.tex.
This script checks every upper exclusion and Gram score, and the exact lower
probability and positive jump. No optimization package is imported.
"""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from fractions import Fraction as Q
from pathlib import Path
import json
from hybrid_verify import verify
from cuberoot_field import F

HERE=Path(__file__).resolve().parent
cover=json.loads((HERE/'cuberoot_exact_cover.json').read_text())
cert=json.loads((HERE/'cuberoot_exact_certificate.json').read_text())
checked=verify(cover,cert)
t=F([0,1,0]);assert t*t*t==4 and 1<t<2 and F(cover['c'])==t
assert list(map(F,cover['cuts']))==[(t+2)/(2*t),2/t,(t+2)/(t*t),t]
a,b,s,d=[Q(v,10**6) for v in [530228,182686,127807,159279]]
assert a+b+s+d==1
beta=a*a*(b+s+d)+2*a*b*(s+d)+2*a*s*d+b*b*d
w=Q(555090,10**6)
lower=(1-(1-beta)*w*w)/(3-3*w+w*w)
upper=Q(checked['exact_bound']);jump=lower-upper
assert jump>Q(6386384,10**10)
saved=json.loads((HERE/'cuberoot_discontinuity.json').read_text())
assert upper==Q(saved['upper']) and lower==Q(saved['uniform_right_lower']) and jump==Q(saved['jump_lower'])
print(json.dumps(dict(upper=str(upper),upper_decimal=float(upper),
    lower=str(lower),lower_decimal=float(lower),jump=str(jump),jump_decimal=float(jump),
    exact_endpoint_and_all_upper_patterns_verified=True),indent=2))
