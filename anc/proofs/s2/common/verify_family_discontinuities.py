"""Exact standard-library verification of alpha3 and subsequent branching jumps.

All endpoint exclusions, sign-space partitions and Gram scores are checked.
Uniform support feasibility of the lower families is proved in
family_discontinuities.tex; fixed masses and recursive probabilities are
independently recomputed here.
"""

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

def check(name):
    assert name in ('alpha3','branch1','branch2','branch3')
    j=None if name=='alpha3' else int(name[6:])
    polynomial=([-2,-1,-1,0,-1,1] if j is None else [-4,0]+[-1]*j+[0,1])
    F=make_field(polynomial);c=F([0,1]+[0]*(len(polynomial)-3))
    cover=read_json(data_path(name+'_exact_cover.json', family="s2"))
    cert=json.loads((data_path(name+'_exact_certificate.json', family="s2")).read_text())
    assert cover['polynomial']==polynomial and F(cover['c'])==c and cover['n']==4
    if name=='alpha3':
        cuts=[2/c,c,1/(c-1),(c+2)/(2*c),(c+2)/(c*c),(c*c+c+2)/(c*(c+2))]
    else:
        r=[F(1)]
        for _ in range(j+2):r.append((1+r[-1])/c)
        b=[4/(c*c)]
        for _ in range(j-1):b.append((1+b[-1])/c)
        cuts=[(c+2)/(2*c)]+r[1:]+b+[c]
    assert list(map(F,cover['cuts']))==sorted(set(cuts))
    checked=verify(cover,cert);upper=Q(checked['exact_bound'])
    record=json.loads((data_path(name+'_lower.json', family="s2")).read_text());assert record['polynomial']==polynomial
    if name=='alpha3':
        p=list(map(Q,record['base_masses']));assert len(p)==6 and sum(p)==1 and min(p)>0
        def success(i,j,k):
            if k>0 and (i==0 or j==0):return True
            if k==5 and min(i,j)<5:return True
            return 0<k<5 and min(i,j)==1 and max(i,j)<k
        base=sum((p[i]*p[j]*p[k] for i,j,k in product(range(6),repeat=3) if success(i,j,k)),Q(0))
        assert base==Q(record['base_success'])
        lower=base/(1-p[0]**3)
    else:
        p=list(map(Q,record['positive_masses']));assert len(p)==j+4 and sum(p)==1 and min(p)>0
        def success(i,j,k):
            return (min(i,j)==0 and max(i,j)<k) or (i==j==1 and k>=3)
        beta=sum((p[i]*p[j]*p[k] for i,j,k in product(range(len(p)),repeat=3) if success(i,j,k)),Q(0))
        assert beta==Q(record['beta']);w=Q(record['scale_mass']);assert 0<w<1
        lower=(1-(1-beta)*w*w)/(3-3*w+w*w)
    assert lower==Q(record['lower']) and lower>upper
    return dict(endpoint=name,polynomial=polynomial,threshold_approx=float(c),
        upper=str(upper),upper_decimal=float(upper),uniform_right_lower=str(lower),
        lower_decimal=float(lower),jump_lower=str(lower-upper),jump_decimal=float(lower-upper),
        patterns=checked['patterns'],exclusions=checked['exclusions'],blocks=checked['blocks'],
        exact_endpoint_and_positive_jump_verified=True)

if __name__=='__main__':
    names=sys.argv[1:] or ['alpha3','branch1','branch2','branch3']
    results=[]
    for name in names:
        row=check(name);results.append(row);print(json.dumps(row,indent=2),flush=True)
    if names==['alpha3','branch1','branch2','branch3']:
        (data_path('family_discontinuities.json', family="s2")).write_text(json.dumps(results,indent=2)+'\n')
