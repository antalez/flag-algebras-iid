"""Exact primal pseudodistribution check for the implemented seven-point SDP.

Reconstructs integer moment matrices from marked flag configurations without
using SDP sparse operators. Fraction-free PSD elimination proves feasibility.
This proves a lower bound on the SDP optimum, not on the iid probability.
"""
import argparse
from fractions import Fraction
from itertools import combinations
import json
from math import comb
from pathlib import Path
import sys

import numpy as np

sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'anton_endpoint'))
from enumerate_patterns import candidates


def validate_full_flag_basis(data,upper):
    """A lower bound must enforce every block of the specified SDP model."""
    if upper.get('format_version') != 2:
        raise ValueError('This primal verifier only supports the version-2 21-block model; extra PSD blocks must not be omitted')
    patterns=[tuple(1 if s=='+' else -1 for s in row) for row in data['patterns']]
    lookup={tuple(t):i for i,t in enumerate(data['tuples'])}
    cache={}
    def induced(vertices):
        if vertices not in cache:
            columns=[lookup[tuple(vertices[i] for i in t)] for t in candidates(len(vertices),False,2)]
            cache[vertices]=[tuple(pattern[i] for i in columns) for pattern in patterns]
        return cache[vertices]
    expected={}
    for t,f in ((2,4),(3,4),(4,5)):
        for roots in combinations(range(6),t):
            types=induced(roots)
            rest=tuple(i for i in range(6) if i not in roots)
            for extra in combinations(rest,f-t):
                left=tuple(sorted(roots+extra))
                marks=tuple(left.index(i) for i in roots)
                for root_type,signature in zip(types,induced(left)):
                    expected.setdefault((t,f,root_type),set()).add((signature,marks))
    actual={}
    for b in upper['inherited']['blocks']:
        key=(b['t'],b['f'],tuple(b['type'] or ()))
        if key in actual:
            raise ValueError('Duplicate primal moment block')
        actual[key]={(tuple(s),tuple(r)) for s,r in b['flags']}
    if actual!=expected:
        raise ValueError('Primal certificate must enforce the full inherited flag basis')
    states={signature for four in combinations(range(6),4) for signature in induced(four)}
    if upper['root_state_count']!=len(states):
        raise ValueError('Root flag basis mismatch')


def positive_semidefinite_bareiss(matrix):
    """Exact PSD test by symmetric fraction-free Schur elimination."""
    if any(int(v)!=v for row in matrix for v in row):
        raise ValueError('Exact PSD elimination requires integer entries')
    a=[[int(v) for v in row] for row in matrix]
    n=len(a)
    if any(len(row)!=n for row in a) or any(a[i][j]!=a[j][i] for i in range(n) for j in range(i)):
        raise ValueError('Moment matrix is not symmetric')
    previous=1
    for k in range(n):
        if any(a[i][i]<0 for i in range(k,n)):
            raise ValueError(f'Negative exact Schur diagonal at step {k}')
        pivots=[i for i in range(k,n) if a[i][i]>0]
        if not pivots:
            if any(a[i][j] for i in range(k,n) for j in range(k,n)):
                raise ValueError('Zero diagonal with nonzero Schur off-diagonal')
            return k
        pivot_index=max(pivots,key=lambda i:a[i][i])
        if pivot_index!=k:
            a[k],a[pivot_index]=a[pivot_index],a[k]
            for row in a:
                row[k],row[pivot_index]=row[pivot_index],row[k]
        pivot=a[k][k]
        for i in range(k+1,n):
            for j in range(i,n):
                numerator=pivot*a[i][j]-a[i][k]*a[j][k]
                quotient,remainder=divmod(numerator,previous)
                if remainder:
                    raise ValueError('Nonintegral Bareiss division')
                a[i][j]=a[j][i]=quotient
        for i in range(k+1,n):
            a[i][k]=a[k][i]=0
        previous=pivot
    return n


def verify_primal(data,states,restrictions,upper,indices,numerators):
    if (upper['coefficient']!=data['coefficient'] or upper.get('summands')!=2
            or data.get('summands')!=2 or data['size']!=6):
        raise ValueError('Model coefficient/arity mismatch')
    validate_full_flag_basis(data,upper)
    if (len(indices)!=len(numerators) or len(set(indices))!=len(indices)
            or any(type(i) is not int or not 0<=i<len(states) for i in indices)
            or any(type(w) is not int or w<0 for w in numerators)
            or sum(numerators)<=0):
        raise ValueError('Invalid rational primal weights')
    denominator=sum(numerators)
    weights6=[0]*len(data['patterns'])
    success_total=0
    for index,weight in zip(indices,numerators):
        for six in restrictions[index]:
            weights6[int(six)]+=weight
            success_total+=weight*data['patterns'][int(six)].count('+')
    support6=[i for i,w in enumerate(weights6) if w]
    patterns=[tuple(1 if s=='+' else -1 for s in data['patterns'][i]) for i in support6]
    weights=[weights6[i] for i in support6]
    lookup={tuple(t):i for i,t in enumerate(data['tuples'])}
    cache={}

    def induced(vertices):
        if vertices not in cache:
            columns=[lookup[tuple(vertices[i] for i in t)] for t in candidates(len(vertices),False,2)]
            cache[vertices]=[tuple(pattern[i] for i in columns) for pattern in patterns]
        return cache[vertices]

    checks=[]
    for block in upper['inherited']['blocks']:
        t,f=block['t'],block['f']
        if not 0<=t<f<=6 or 2*f-t>6:
            raise ValueError('Invalid flag dimensions')
        flags={(tuple(s),tuple(r)):i for i,(s,r) in enumerate(block['flags'])}
        if len(flags)!=len(block['flags']):
            raise ValueError('Duplicate flags')
        dim=len(flags)
        matrix=[[0]*dim for _ in range(dim)]
        root_type=tuple(block['type'] or ())
        for roots in combinations(range(6),t):
            allowed=[j for j,s in enumerate(induced(roots)) if s==root_type]
            rest=tuple(i for i in range(6) if i not in roots)
            for extra in combinations(rest,f-t):
                left=tuple(sorted(roots+extra))
                lm=tuple(left.index(i) for i in roots)
                a=[flags.get((s,lm),-1) for s in induced(left)]
                for other in combinations(tuple(i for i in rest if i not in extra),f-t):
                    right=tuple(sorted(roots+other))
                    rm=tuple(right.index(i) for i in roots)
                    b=[flags.get((s,rm),-1) for s in induced(right)]
                    for j in allowed:
                        if a[j]>=0 and b[j]>=0:
                            matrix[a[j]][b[j]]+=weights[j]
        rank=positive_semidefinite_bareiss(matrix)
        norm=7*comb(6,t)*comb(6-t,f-t)*comb(6-f,f-t)*denominator
        checks.append(dict(t=t,f=f,type=block['type'],dimension=dim,rank=rank,
                           exact_psd=True,moment_denominator=str(norm)))
    dim=4*upper['root_state_count']
    matrix=[[0]*dim for _ in range(dim)]
    fours=list(combinations(range(7),4))
    four_lookup={q:i for i,q in enumerate(fours)}
    for root in range(7):
        rest=tuple(i for i in range(7) if i!=root)
        for extra in combinations(rest,3):
            left=tuple(sorted((root,)+extra))
            right=tuple(sorted((root,)+tuple(i for i in rest if i not in extra)))
            for index,weight in zip(indices,numerators):
                a=4*int(states[index,four_lookup[left]])+left.index(root)
                b=4*int(states[index,four_lookup[right]])+right.index(root)
                matrix[a][b]+=weight
    rank=positive_semidefinite_bareiss(matrix)
    checks.append(dict(t=1,f=4,type=None,dimension=dim,rank=rank,exact_psd=True,
                       moment_denominator=str(140*denominator)))
    lower=Fraction(success_total,420*denominator)
    upper_value=Fraction(upper['exact_bound'])
    if lower>upper_value:
        raise ValueError('Primal value exceeds certified dual upper bound')
    return dict(exact_lower=str(lower),lower=float(lower),exact_upper=str(upper_value),
                upper=float(upper_value),exact_gap=str(upper_value-lower),gap=float(upper_value-lower),
                weight_denominator=str(denominator),blocks=checks,exact_psd=True,
                interpretation='Bounds on the implemented SDP optimum, not an achieved iid lower bound')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6',type=Path,required=True)
    p.add_argument('--cover7',type=Path,required=True)
    p.add_argument('--upper-certificate',type=Path,required=True)
    p.add_argument('--primal',type=Path,required=True)
    args=p.parse_args()
    data=json.loads(args.cover6.read_text())
    with np.load(args.cover7) as archive:
        states,restrictions=archive['states'],archive['restrictions']
    upper=json.loads(args.upper_certificate.read_text())
    from verify_sdp7 import verify
    verify(data,states,restrictions,upper)
    saved=json.loads(args.primal.read_text())
    if saved['coefficient']!=data['coefficient']:
        raise ValueError('Primal coefficient mismatch')
    result=verify_primal(data,states,restrictions,upper,saved['indices'],saved['weight_numerators'])
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
