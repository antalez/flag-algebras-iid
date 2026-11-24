"""Standard-library exact verifier for ordered ratio/additive flag certificates."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from fractions import Fraction as Q
from itertools import combinations
from math import comb,lcm
from collections import Counter
from pathlib import Path
import json

def read_json(path):
    """Read a proof artifact, explaining how to fetch an unexpanded LFS pointer."""
    path=Path(path)
    with path.open() as stream:
        first=stream.readline()
        if first.strip()=='version https://git-lfs.github.com/spec/v1':
            raise SystemExit(
                f'{path} is a Git LFS pointer; the proof data has not been fetched.\n'
                'From the repository root, run:\n'
                '  git lfs install\n'
                '  git lfs pull\n'
                'Then rerun this command.')
        stream.seek(0)
        return json.load(stream)

def forms(n,cuts):
    return ([('pair',i,j,q) for i,j in combinations(range(n),2) for q in range(len(cuts))]
        +[('sum',i,j,k) for i,j in combinations(range(n),2) for k in range(n) if k>i and k!=j])

def cover_forms(cover):
    canonical=forms(cover['n'],cover['cuts'])
    ordered=list(map(tuple,cover.get('form_order',canonical)))
    assert len(ordered)==len(canonical) and set(ordered)==set(canonical)
    return ordered

def block_cut_indices(block,cuts):
    """Interpret a flag block using any fixed subset of the cover cutoffs."""
    indices=tuple(block.get('cut_indices',range(len(cuts))))
    assert all(type(i)==int and 0<=i<len(cuts) for i in indices)
    assert indices==tuple(sorted(set(indices)))
    return indices

def gap_rows(n,c,cuts):
    rows=[]
    for kind,i,j,k in forms(n,cuts):
        x=[Q(0)]*n
        if kind=='pair':x[j]=1;x[i]=-cuts[k]
        else:x[i]+=1;x[j]+=1;x[k]-=c
        row=[sum(x[h:]) for h in range(n)]
        den=lcm(*(v.denominator for v in row));rows.append([int(v*den) for v in row])
    return rows

def verify(cover,cert,*,return_values=False):
    n=cover['n'];algebraic=cover.get('field') in ('cuberoot4','algebraic')
    ff=cover_forms(cover)
    if algebraic:
        if cover['field']=='cuberoot4':
            from cuberoot_field import F
        else:
            from algebraic_field import make_field
            F=make_field(cover['polynomial'])
        c=F(cover['c']);cuts=list(map(F,cover['cuts']));number=F
        rows=[]
        for kind,i,j,k in ff:
            x=[F(0)]*n
            if kind=='pair':x[j]=F(1);x[i]=-cuts[k]
            else:x[i]+=1;x[j]+=1;x[k]-=c
            rows.append([sum(x[h:]) for h in range(n)])
    else:
        c=Q(cover['c']);cuts=list(map(Q,cover['cuts']));number=Q
        rows=gap_rows(n,c,cuts)
        canonical=forms(n,cuts);rows=[rows[canonical.index(f)] for f in ff]
    assert 1<c<2 and all(v>1 for v in cuts) and cuts==sorted(set(cuts))
    width=len(rows);intervals=[]
    def interval(prefix):
        assert len(prefix)<=width and set(prefix)<=set('+-')
        start=int(''.join('1' if s=='+' else '0' for s in prefix),2)<<(width-len(prefix))
        return start,start+(1<<(width-len(prefix)))
    for prefix,weights in cover['pruned'].items():
        weights={int(i):number(v) for i,v in weights.items()}
        assert weights and all(0<=i<len(prefix) and v>0 for i,v in weights.items())
        assert all(sum(w*(1 if prefix[i]=='+' else -1)*rows[i][h] for i,w in weights.items())>=0 for h in range(n))
        intervals.append(interval(prefix))
    for pat in cover['patterns']:
        assert len(pat)==width;intervals.append(interval(pat))
    end=0
    for a,b in sorted(intervals):assert a==end;end=b
    assert end==1<<width
    assert cert['n']==n and cert['c']==cover['c'] and cert['cuts']==cover['cuts']
    lookup={f:i for i,f in enumerate(ff)}
    for block in cert['blocks']:
        t,f=block['t'],block['f'];assert 0<=t<f and 2*f-t<=n
        indices=block_cut_indices(block,cuts)
        flags=block['flags'];L=block['factor'];den=block['denominator']
        assert len(set(flags))==len(flags)==len(L) and den>0
        assert len(set(map(len,L)))==1 and all(type(v)==int for row in L for v in row)
        assert all(0<=v<(1<<len(forms(f,indices)))*comb(f,t) for v in flags)
        assert 0<=block['type']<1<<len(forms(t,indices))
    values=[]
    for pat in cover['patterns']:
        cache={}
        def code(vertices,indices):
            key=(vertices,indices)
            if key not in cache:
                out=0
                for bit,(kind,i,j,k) in enumerate(forms(len(vertices),indices)):
                    form=(kind,vertices[i],vertices[j],indices[k] if kind=='pair' else vertices[k])
                    if pat[lookup[form]]=='+':out+=1<<bit
                cache[key]=out
            return cache[key]
        value=Q(sum(pat[i]=='+' for i,f in enumerate(ff) if f[0]=='sum'),3*comb(n,3))
        for block in cert['blocks']:
            t,f=block['t'],block['f'];marks=list(combinations(range(f),t))
            indices=block_cut_indices(block,cuts)
            flags={v:i for i,v in enumerate(block['flags'])};counts=Counter()
            for roots in combinations(range(n),t):
                if code(roots,indices)!=block['type']:continue
                rest=tuple(i for i in range(n) if i not in roots)
                for ae in combinations(rest,f-t):
                    a=tuple(sorted(roots+ae));ac=code(a,indices)*len(marks)+marks.index(tuple(a.index(i) for i in roots))
                    for be in combinations(tuple(i for i in rest if i not in ae),f-t):
                        b=tuple(sorted(roots+be));bc=code(b,indices)*len(marks)+marks.index(tuple(b.index(i) for i in roots))
                        # Missing flags are interpreted as zero coordinates.
                        if ac in flags and bc in flags:counts[flags[ac],flags[bc]]+=1
            L=block['factor']
            numerator=sum(count*sum(a*b for a,b in zip(L[i],L[j])) for (i,j),count in counts.items())
            value+=Q(numerator,block['denominator']**2*comb(n,t)*comb(n-t,f-t)*comb(n-f,f-t))
        values.append(value)
    bound=max(values)
    if 'bound' in cert:assert bound==Q(cert['bound'])
    result=dict(exact_bound=str(bound),decimal=float(bound),patterns=len(values),
        exclusions=len(cover['pruned']),blocks=[len(b['flags']) for b in cert['blocks']],
        completeness_verified=True,PSD_by_rational_Gram_factors=True)
    if return_values:result['values']=values
    return result

if __name__=='__main__':
    import sys
    here=Path(__file__).resolve().parent
    stem=sys.argv[1] if len(sys.argv)>1 else 'hybrid_exact'
    cover=read_json(here/(stem+'_cover.json'))
    cert=read_json(here/(stem+'_certificate.json'))
    print(json.dumps(verify(cover,cert),indent=2))
