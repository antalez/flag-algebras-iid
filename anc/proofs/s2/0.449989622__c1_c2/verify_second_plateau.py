"""Standard-library exact verification of the second plateau certificate."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
import json
import os
import sys
from itertools import combinations
from math import comb
from pathlib import Path
from fractions import Fraction as Q

from algebraic_field import make_field
from hybrid_verify import verify, forms, cover_forms, block_cut_indices
from verify_near_small import scalar_features, scalar_profile

HERE=Path(__file__).resolve().parent
F=make_field([-403,0,1],root_interval=(20,21))
ROOT=F([0,1]); B=2*(ROOT-14)/27


def progress(message):
    if os.environ.get('PLATEAU_PROGRESS'):
        print(message,file=sys.stderr,flush=True)


def positive_definite(Y):
    a=[row[:] for row in Y]
    for k in range(len(a)):
        assert a[k][k]>0
        for i in range(k+1,len(a)):
            for j in range(i,len(a)):
                a[i][j]=a[j][i]=a[i][j]-a[i][k]*a[k][j]/a[k][k]


def verify_exact(cover,cert,*,field=F,bound=B,scale=None,beta=Q(4,27),
                 endpoint=(-2,-1,0,1),expected_c=('0','1','0'),
                 expected_cuts=(('-1','0','1'),('0','1','0')),minimum_margin=Q(1,200),
                 psd_check=positive_definite):
    F=field;B=bound
    n=cover['n'];assert n in (4,5)
    scale=(32-ROOT)/23 if scale is None else scale
    assert 0<scale<1
    assert (1-(1-F(beta))*scale**2)/(3-3*scale+scale**2)==B
    # The existing verifier checks the entire cover, using the endpoint field.
    verify(cover,dict(n=n,c=cover['c'],cuts=cover['cuts'],blocks=[]))
    progress('Exact pattern cover verified')
    assert cover['polynomial']==list(endpoint) and cover['c']==list(expected_c)
    assert cover['cuts']==list(map(list,expected_cuts))
    blocks=[]
    for block in cert['blocks']:
        indices=block_cut_indices(block,cover['cuts'])
        t,f=block['t'],block['f'];assert 0<=t<f and 2*f-t<=n
        assert 0<=block['type']<1<<len(forms(t,indices))
        assert all(type(v)==int and 0<=v<(1<<len(forms(f,indices)))*comb(f,t)
                   for v in block['flags'])
        W=[[F(v) for v in row] for row in block['W']]
        Y=[[F(v) for v in row] for row in block['Y']]
        assert Y and all(len(row)==len(Y) for row in Y)
        assert all(Y[i][j]==Y[j][i] for i in range(len(Y)) for j in range(len(Y)))
        assert len(W)==len(block['flags']) and all(len(row)==len(Y) for row in W)
        psd_check(Y)
        WY=[[sum((W[i][a]*Y[a][b] for a in range(len(Y)) if W[i][a] and Y[a][b]),F(0))
             for b in range(len(Y))] for i in range(len(W))]
        Z=[[sum((WY[i][b]*W[j][b] for b in range(len(Y)) if WY[i][b] and W[j][b]),F(0))
            for j in range(len(W))] for i in range(len(W))]
        blocks.append((block,Z))
        progress(f"Exact PSD and flag block {len(blocks)}/{len(cert['blocks'])} verified")
    mult=[F(v) for v in cert['multipliers']]
    profile=scalar_profile(cert)
    f0=scalar_features(cover,Q(0),**profile)
    f1=scalar_features(cover,Q(1),**profile)
    assert len(mult)==len(f0[0]) and all(v>=0 for v in mult)
    ff=cover_forms(cover)
    lookup={f:i for i,f in enumerate(ff)}
    vals=[]; ends=[]
    for ix,pat in enumerate(cover['patterns']):
        cache={}
        def code(vertices,indices):
            key=(vertices,indices)
            if key not in cache:
                cache[key]=sum(
                    1<<bit for bit,(kind,i,j,k) in enumerate(forms(len(vertices),indices))
                    if pat[lookup[kind,vertices[i],vertices[j],
                                  indices[k] if kind=='pair' else vertices[k]]]=='+')
            return cache[key]
        value=F(Q(sum(pat[i]=='+' for i,f in enumerate(ff) if f[0]=='sum'),
                  3*comb(n,3)))
        for block,Z in blocks:
            t,f=block['t'],block['f'];assert 0<=t<f and 2*f-t<=n
            indices=block_cut_indices(block,cover['cuts'])
            flags={v:i for i,v in enumerate(block['flags'])};assert len(flags)==len(block['flags'])
            marks=list(combinations(range(f),t));total=F(0)
            for roots in combinations(range(n),t):
                if code(roots,indices)!=block['type']:continue
                rest=tuple(i for i in range(n) if i not in roots)
                for ext in combinations(rest,f-t):
                    a=tuple(sorted(roots+ext));ac=code(a,indices)*len(marks)+marks.index(tuple(a.index(i) for i in roots))
                    for ext2 in combinations(tuple(i for i in rest if i not in ext),f-t):
                        b=tuple(sorted(roots+ext2));bc=code(b,indices)*len(marks)+marks.index(tuple(b.index(i) for i in roots))
                        if ac in flags and bc in flags:total+=Z[flags[ac]][flags[bc]]
            value+=total/(comb(n,t)*comb(n-t,f-t)*comb(n-f,f-t))
        intercept=value;slope=F(0)
        for j,m in enumerate(mult):
            intercept+=m*(F(f0[ix][j][0])+B*F(f1[ix][j][0]-f0[ix][j][0]))
            slope+=m*F(f0[ix][j][1])
        vals.append(intercept+B*slope);ends.append(intercept+F(Q(2,3))*slope)
        if (ix+1)%250==0:progress(f'Checked {ix+1}/{len(cover["patterns"])} pattern scores')
    assert max(vals)==B
    margin=F(Q(2,3))-max(ends);assert margin>minimum_margin
    result=dict(patterns=len(vals),equality_patterns=sum(v==B for v in vals),
                reduced_dimensions=[len(b['Y']) for b in cert['blocks']],
                bound=B.json(),bound_decimal=float(B),second_endpoint_margin=margin.json(),
                second_endpoint_margin_decimal=float(margin),all_exact_checks_passed=True)
    return result


if __name__=='__main__':
    cover=json.loads((HERE/'near_c2_exact_cover.json').read_text())
    cert=json.loads((HERE/'second_plateau_exact_certificate.json').read_text())
    result=verify_exact(cover,cert)
    (HERE/'second_plateau_exact_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
