"""Check the improved alpha3 jump using the exact plateau certificate.

Run verify_alpha3_plateau.py separately to verify the endpoint upper value.
The right-hand support feasibility is proved in family_discontinuities.tex.
"""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
import json
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from verify_alpha3_plateau import F, B

record=json.loads(Path(__file__).with_name('alpha3_lower.json').read_text())
assert record['polynomial']==[-2,-1,-1,0,-1,1]
p=list(map(Q,record['base_masses']))
assert len(p)==6 and sum(p)==1 and min(p)>0


def success(i,j,k):
    if k>0 and (i==0 or j==0):return True
    if k==5 and min(i,j)<5:return True
    return 0<k<5 and min(i,j)==1 and max(i,j)<k


base=sum((p[i]*p[j]*p[k] for i,j,k in product(range(6),repeat=3)
          if success(i,j,k)),Q(0))
assert base==Q(record['base_success'])
lower=base/(1-p[0]**3)
assert lower==Q(record['lower'])
jump=F(lower)-B
assert jump>Q(593771,10**9)
print('Verified right-hand lower construction:',float(lower))
print('Verified alpha3 jump > 0.000593771, assuming the separately checked exact plateau')
