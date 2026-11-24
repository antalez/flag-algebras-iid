"""Standard-library exact checks of colored four-point proofs at c4,c5,c6."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from anc.proofs.paths import data_path
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json,sys
from algebraic_field import make_field
from hybrid_verify import verify,read_json
HERE=Path(__file__).resolve().parent

def check(n):
    assert n in (4,5,6);name='ladder'+str(n)
    polynomial=[-2]+[-1]*(n-1)+[0,1];F=make_field(polynomial);c=F([0,1]+[0]*(n-1))
    cover=read_json(data_path(name+'_exact_cover.json', family="s2"))
    cert=json.loads((data_path(name+'_exact_certificate.json', family="s2")).read_text())
    assert cover['polynomial']==polynomial and cover['n']==4 and F(cover['c'])==c
    r=[F(1)]
    for _ in range(n):r.append((1+r[-1])/c)
    assert r[-1]==c
    b=[4/(c*c)]
    for _ in range(n-4):b.append((1+b[-1])/c)
    cuts=sorted(set([(c+2)/(2*c)]+r[1:]+b+[c]))
    assert list(map(F,cover['cuts']))==cuts
    result=verify(cover,cert);upper=Q(result['exact_bound'])
    law=json.loads((data_path(name+'_lower.json', family="s2")).read_text());assert law['polynomial']==polynomial
    p=list(map(Q,law['positive_masses']));w=Q(law['scale_mass'])
    assert len(p)==n+1 and sum(p)==1 and min(p)>0 and 0<w<1
    B=sum((p[i]*p[j]*p[k] for i,j,k in product(range(n+1),repeat=3)
        if (min(i,j)==0 and max(i,j)<k) or (i==j==1 and k>=4)),Q(0))
    assert B==Q(law['beta']);lower=(1-(1-B)*w*w)/(3-3*w+w*w)
    assert lower==Q(law['lower']) and lower>upper
    return dict(endpoint='c'+str(n),polynomial=polynomial,threshold_approx=float(c),
        upper=str(upper),upper_decimal=float(upper),uniform_right_lower=str(lower),lower_decimal=float(lower),
        jump_lower=str(lower-upper),jump_decimal=float(lower-upper),patterns=result['patterns'],
        exclusions=result['exclusions'],blocks=result['blocks'],exact_endpoint_and_positive_jump_verified=True)

if __name__=='__main__':
    ns=list(map(int,sys.argv[1:])) or [4,5,6];rows=[]
    for n in ns:
        row=check(n);rows.append(row);print(json.dumps(row,indent=2),flush=True)
    if ns==[4,5,6]:(data_path('ladder_discontinuities.json', family="s2")).write_text(json.dumps(rows,indent=2)+'\n')
