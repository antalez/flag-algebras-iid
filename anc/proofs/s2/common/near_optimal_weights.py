"""Exact five-point weights for degree and lower-tail constraints.

Conditioning on the root makes the weight draws independent of the draws
testing its degree or lower tail. No numerical or solver dependency is used.
"""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from fractions import Fraction as Q
from itertools import combinations
from math import comb

from hybrid_verify import cover_forms


def degree_flag_counts(cover):
    """Count rooted three-point classes and their disjoint degree tests."""
    n=cover['n'];assert n>=5
    lookup={form:i for i,form in enumerate(cover_forms(cover))}
    subforms=[('pair',i,j,k) for i,j in combinations(range(3),2)
              for k in range(len(cover['cuts']))]
    subforms += [('sum',i,j,k) for i,j in combinations(range(3),2)
                 for k in range(3) if k>i and k!=j]
    choices=[]
    for root in range(n):
        for auxiliary in combinations([i for i in range(n) if i!=root],2):
            vertices=tuple(sorted((root,)+auxiliary))
            indices=[lookup[kind,vertices[i],vertices[j],
                            k if kind=='pair' else vertices[k]]
                     for kind,i,j,k in subforms]
            extensions=list(combinations([i for i in range(n)
                                          if i not in vertices],2))
            choices.append((root,vertices.index(root),indices,extensions))
    rows=[];keys=set()
    for pattern in cover['patterns']:
        counts={}
        for root,mark,indices,extensions in choices:
            key=3*sum(1<<bit for bit,index in enumerate(indices)
                      if pattern[index]=='+')+mark
            weight,degree=counts.get(key,(0,0))
            for extension in extensions:
                vertices=tuple(sorted((root,)+extension))
                score=sum(pattern[lookup['sum',*sorted(i for i in vertices if i!=target),
                                         target]]=='+'
                          for target in vertices if target>vertices[0])
                weight+=1;degree+=score
            counts[key]=(weight,degree);keys.add(key)
        rows.append(counts)
    norm=n*comb(n-1,2)*comb(n-3,2)
    return sorted(keys),rows,norm


def weighted_threshold_features(cover, lower, *, full_near_optimality):
    """Partition each lower-tail test by an independent root/point class."""
    n=cover['n'];assert n>=5
    if cover.get('field')=='algebraic':
        from algebraic_field import make_field
        field=make_field(cover['polynomial'])
    elif cover.get('field')=='cuberoot4':
        from cuberoot_field import F as field
    else:
        field=Q
    cuts=[field(q) for q in cover['cuts']]
    qs=sorted(set([field(1)]+cuts+[1/q for q in cuts]))
    thresholds=[(0,None) if q==1 else
                (1,cuts.index(q)) if q>1 else (-1,cuts.index(1/q))
                for q in qs]
    lookup={form:i for i,form in enumerate(cover_forms(cover))}
    choices=[(z,y,tuple(sorted((z,y))),
              list(combinations([i for i in range(n) if i not in (z,y)],3)))
             for z in range(n) for y in range(n) if z!=y]
    classes=2*(len(cuts)+1)
    norm=n*(n-1)*comb(n-2,3)
    rows=[]
    for pattern in cover['patterns']:
        def win(a,b,target):
            a,b=sorted((a,b))
            return int(target>a and pattern[lookup['sum',a,b,target]]=='+')
        def below(i,z,mode,cutoff):
            if mode==0:return i<z
            if mode>0:return i<z or pattern[lookup['pair',z,i,cutoff]]=='+'
            return i<z and pattern[lookup['pair',i,z,cutoff]]=='-'
        counts=[[[0,0,0] for _ in range(classes)] for _ in thresholds]
        for z,y,(lo,hi),extensions in choices:
            group=2*sum(pattern[lookup['pair',lo,hi,k]]=='-'
                        for k in range(len(cuts)))+int(z>y)
            for vertices in extensions:
                score=sum(win(*[i for i in vertices if i!=target],target)
                          for target in vertices)
                for q,(mode,cutoff) in enumerate(thresholds):
                    bs=[below(i,z,mode,cutoff) for i in vertices]
                    allbelow=int(all(bs))
                    values=counts[q][group]
                    values[0]+=allbelow;values[1]+=allbelow*score
                    values[2]+=int(bs[1] and not bs[2])*win(
                        vertices[0],vertices[2],vertices[1])
        features=[]
        for groups in counts:
            for weight,success,crossing in groups:
                weight=Q(weight,norm);success=Q(success,3*norm)
                crossing=Q(crossing,3*norm)
                features.extend([(-success,weight),
                                 (success+crossing,-weight) if full_near_optimality
                                 else (success+crossing-lower*weight,Q(0))])
        rows.append(features)
    return rows
