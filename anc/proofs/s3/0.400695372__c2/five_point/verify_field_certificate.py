"""Exact standard-library verification of the Q(r) five-point certificate."""
import argparse,json
from fractions import Fraction as Q
from itertools import combinations
from math import comb
from pathlib import Path
from exact_cover import verify as verify_cover
from field import F, BSTAR, positive_definite
HERE=Path(__file__).resolve().parent

def forms(n):
    return [('p',(i,j),0) for i,j in combinations(range(n),2)]+[('a',v,k) for v in combinations(range(n),4) for k in (2,3)]

def verify(cert,cover):
    complete=verify_cover(cover);assert cover['n']==5 and list(map(Q,cover['cuts']))==[Q(2)]
    lower=BSTAR
    assert cert['polynomial']==[2,-2,-3,-4,1]
    mult=list(map(F,cert['multipliers']));assert len(mult)==len(cert['features']) and len(set(cert['features']))==len(mult) and min(mult)>=0
    ff=forms(5);lookup={v:i for i,v in enumerate(ff)}
    # Positivity of each reduced Y proves PSD of W Y W^T.
    blocks=[]
    for b in cert['blocks']:
        assert 0<=b['t']<b['f']<=4 and 2*b['f']-b['t']<=5
        W=[[F(v) for v in row] for row in b['basis']]
        Y=[[F(v) for v in row] for row in b['matrix']]
        assert W and all(len(row)==len(Y) for row in W)
        positive_definite(Y)
        WY=[[sum((a*c for a,c in zip(row,col)),F(0)) for col in zip(*Y)] for row in W]
        G=[[sum((a*c for a,c in zip(row,col)),F(0)) for col in W] for row in WY]
        assert len(G)==len(b['flags']) and len(set(b['flags']))==len(G)
        blocks.append((b,G,{v:i for i,v in enumerate(b['flags'])}))
    affine=[]
    for pattern in cover['patterns']:
        signs=[1 if s=='+' else -1 for s in pattern];cache={}
        def code(v):
            if v not in cache:cache[v]=sum((1<<j) for j,(kind,inds,k) in enumerate(forms(len(v))) if signs[lookup[kind,tuple(v[i] for i in inds),k]]==1)
            return cache[v]
        def score(v):return Q(sum(signs[lookup['a',v,k]]==1 for k in (2,3)),4)
        obj=sum((score(v) for v in combinations(range(5),4)),Q(0))/5
        def below(i,z,q):
            if q==1:return i<z
            if q==2:return i<z or signs[lookup['p',(z,i),0]]==1
            assert q==Q(1,2)
            return i<z and signs[lookup['p',(i,z),0]]==-1
        feats=[];slopes=[];names=[]
        for q in [Q(1,2),Q(1),Q(2)]:
            nn=gg=bc=Q(0)
            for z in range(5):
                v=tuple(i for i in range(5) if i!=z);lo=[below(i,z,q) for i in v]
                nn+=all(lo);gg+=all(lo)*score(v);bc+=Q(lo[2] and not lo[3] and signs[lookup['a',v,2]]==1,4)
            nn/=5;gg/=5;bc/=5
            feats.extend([lower*nn-gg,gg+bc-lower*nn]);slopes.extend([nn,Q(0)])
            names.extend([f'sublaw:q={float(q)}:class=0',f'substitution:q={float(q)}:class=0'])
        groups={}
        for z in range(5):
            for y in range(5):
                if y==z:continue
                pair=tuple(sorted((z,y)));cl=code(pair)*2+pair.index(z)
                if cl not in groups:groups[cl]=[Q(0),Q(0)]
                groups[cl][0]+=Q(1,20);groups[cl][1]+=score(tuple(i for i in range(5) if i!=y))/20
        # Match features by explicit name, independently of enumeration order.
        for cl in range(4):
            kk,dd=groups.get(cl,(Q(0),Q(0)));feats.extend([dd-lower*kk,lower*kk-dd]);slopes.extend([Q(0),kk]);names.extend([f'degree_low:f=2:class={cl}',f'degree_high:f=2:class={cl}'])
        fmap=dict(zip(names,zip(feats,slopes)));a=obj;bcoef=Q(0)
        for name,w in zip(cert['features'],mult):
            feature,slope=fmap[name];a+=w*(feature-lower*slope);bcoef+=w*slope
        for block,G,flagmap in blocks:
            t=block['t'];f=block['f'];marks=list(combinations(range(f),t));count=0
            for roots in combinations(range(5),t):
                if code(roots)!=block['type']:continue
                rest=tuple(i for i in range(5) if i not in roots)
                for ae in combinations(rest,f-t):
                    av=tuple(sorted(roots+ae));ac=code(av)*len(marks)+marks.index(tuple(av.index(i) for i in roots))
                    for be in combinations(tuple(i for i in rest if i not in ae),f-t):
                        bv=tuple(sorted(roots+be));bc=code(bv)*len(marks)+marks.index(tuple(bv.index(i) for i in roots))
                        count+=G[flagmap[ac]][flagmap[bc]]
            norm=comb(5,t)*comb(5-t,f-t)*comb(5-f,f-t)
            a+=F(count)/norm
        affine.append((a,bcoef))
    at_one=max(a+b for a,b in affine);assert at_one<1
    scores=[a+b*lower for a,b in affine]
    for i,value in enumerate(scores):
        assert value<=lower,('score exceeds Bstar',i,float(value-lower))
    assert 1-at_one>=Q(8343,5000000)*(1-lower)
    assert 1-at_one>Q(9,10000)
    return dict(**complete,blocks=len(blocks),original_dimensions=[len(b['basis']) for b in cert['blocks']],reduced_dimensions=[len(b['matrix']) for b in cert['blocks']],bound=lower.json(),bound_decimal=float(lower),tight_patterns=sum(v==lower for v in scores),margin_at_one=(1-at_one).json(),margin_at_one_decimal=float(1-at_one),exact_algebraic_upper_verified=True,proves_equality=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--certificate',default='n5_field_certificate.json');args=ap.parse_args()
    cert=json.loads((HERE/args.certificate).read_text());cover=json.loads((HERE/'n5_cut2_exact_cover.json').read_text());result=verify(cert,cover)
    print(json.dumps(result,indent=2))
