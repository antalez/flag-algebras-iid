"""Generate/check a rational complete five-point colored pattern cover.

The search uses SciPy. The --verify path uses only Python's standard library.
This certifies pattern completeness, not the numerical SDP matrices.
"""
import argparse,json
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
HERE=Path(__file__).resolve().parent

def rows(n,cuts):
    out=[]
    for i,j in combinations(range(n),2):
        for q in cuts:
            v=[Q(0)]*n;v[j]=1;v[i]=-q;out.append(v)
    for v in combinations(range(n),4):
        for k in (2,3):
            row=[Q(0)]*n
            for i in v:row[i]=1
            row[v[k]]=-2;out.append(row)
    return [[sum(row[j:]) for j in range(n)] for row in out]

def verify(data):
    n=data['n'];rr=rows(n,list(map(Q,data['cuts'])));width=len(rr)
    pats=set(data['patterns']);pruned=data['pruned'];assert len(pats)==len(data['patterns'])
    for prefix,proof in pruned.items():
        assert len(prefix)<=width and set(prefix)<=set('+-')
        weights={int(k):Q(v) for k,v in proof.items()};assert weights and min(weights.values())>0
        assert all(0<=k<len(prefix) for k in weights)
        assert all(sum(w*(1 if prefix[k]=='+' else -1)*rr[k][j] for k,w in weights.items())>=0 for j in range(n))
    usedp=set();usede=set()
    def visit(prefix):
        if prefix in pruned:usede.add(prefix);return
        if len(prefix)==width:assert prefix in pats;usedp.add(prefix);return
        visit(prefix+'+');visit(prefix+'-')
    visit('');assert usedp==pats and usede==set(pruned)
    return dict(patterns=len(pats),excluded_prefixes=len(pruned),complete_cover_verified=True)

def generate(n,cuts):
    import numpy as np
    from scipy.optimize import linprog
    rr=rows(n,cuts);A=np.array(rr,dtype=float);out=dict(n=n,cuts=list(map(str,cuts)),patterns=[],pruned={})
    def dfs(signs):
        h=A[:len(signs)]*np.array(signs)[:,None]
        mat=np.vstack([np.c_[h,np.ones(len(signs))],np.c_[-np.eye(n),np.ones(n)]])
        lp=linprog([0]*n+[-1],A_ub=mat,b_ub=np.zeros(len(mat)),A_eq=[[1]*n+[0]],b_eq=[1],bounds=[(0,1)]*(n+1),method='highs')
        prefix=''.join('+' if x==1 else '-' for x in signs)
        if not lp.success or lp.x[-1]<1e-8:
            ex=linprog(np.zeros(len(signs)),A_ub=-h.T,b_ub=np.zeros(n),A_eq=np.ones((1,len(signs))),b_eq=[1],bounds=(0,None),method='highs')
            if ex.success:
                for den in [100,10000,1000000]:
                    w={i:Q(float(v)).limit_denominator(den) for i,v in enumerate(ex.x) if v>1e-10}
                    if w and min(w.values())>0 and all(sum(v*signs[i]*rr[i][j] for i,v in w.items())>=0 for j in range(n)):
                        out['pruned'][prefix]={str(k):str(v) for k,v in w.items()};return
        if len(signs)==len(rr):out['patterns'].append(prefix);return
        dfs(signs+[1]);dfs(signs+[-1])
    dfs([]);return out

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--verify',action='store_true');args=ap.parse_args();path=HERE/'n5_cut2_exact_cover.json'
    if not args.verify:
        data=generate(5,[Q(2)]);print(verify(data));path.write_text(json.dumps(data,indent=2)+'\n')
    else:print(json.dumps(verify(json.loads(path.read_text())),indent=2))
