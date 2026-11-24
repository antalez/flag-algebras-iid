"""Exact rational verification of small near-optimal S2 certificates.

No solver or NumPy is used. Completeness is checked over the endpoint field;
Gram matrices, scalar coefficients, and both endpoint scores are rational.
"""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
import argparse
import json
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb
from pathlib import Path

from hybrid_verify import cover_forms, read_json, verify


def scalar_features(cover, lower, *, full_near_optimality=False,
                    degree_flag_weights=False, weighted_thresholds=False):
    n = cover['n']
    if cover.get('field') == 'algebraic':
        from algebraic_field import make_field
        field = make_field(cover['polynomial'])
    elif cover.get('field') == 'cuberoot4':
        from cuberoot_field import F as field
    else:
        field = Q
    cuts = list(map(field, cover['cuts']))
    qs = sorted(set([field(1)] + cuts + [1/q for q in cuts]))
    # Threshold comparisons and inversion depend only on the cover, not on
    # its patterns. Keep algebraic arithmetic out of the counting loops.
    thresholds=[(0,None) if q==1 else
                ((1,cuts.index(q)) if q>1 else (-1,cuts.index(1/q)))
                for q in qs]
    lookup = {f: i for i, f in enumerate(cover_forms(cover))}
    triples={z:list(combinations([i for i in range(n) if i!=z],3))
             for z in range(n)}
    degree_terms=[(z,y,lo,hi,list(combinations(
        [i for i in range(n) if i not in (z,y)],2)))
        for z in range(n) for y in range(n) if z!=y
        for lo,hi in [sorted((z,y))]]
    rows = []
    for pat in cover['patterns']:
        def win(a, b, z):
            a, b = sorted((a, b))
            return int(z > a and pat[lookup['sum', a, b, z]] == '+')
        scores={v:sum(win(*[i for i in v if i!=z],z) for z in v)
                for v in combinations(range(n),3)}
        def below(i, z, mode, cutoff):
            if mode == 0:
                return i < z
            if mode > 0:
                return i < z or pat[lookup['pair', z, i, cutoff]] == '+'
            return i < z and pat[lookup['pair', i, z, cutoff]] == '-'
        features = []
        for mode,cutoff in thresholds:
            nn=gg=bc=0
            for z in range(n):
                for v in triples[z]:
                    bs=[below(i,z,mode,cutoff) for i in v]
                    allbelow=int(all(bs))
                    nn+=allbelow
                    gg+=allbelow*scores[v]
                    bc+=int(bs[1] and not bs[2])*win(v[0],v[2],v[1])
            norm = n*comb(n-1, 3)
            nn=Q(nn,norm);gg=Q(gg,3*norm);bc=Q(bc,3*norm)
            features.extend([(-gg, nn),
                             (gg+bc, -nn) if full_near_optimality else
                             (gg+bc-lower*nn, Q(0))])
        groups={j:[0,0] for j in range(2*(len(cuts)+1))}
        for z,y,lo,hi,extensions in degree_terms:
            j=2*sum(pat[lookup['pair',lo,hi,k]]=='-' for k in range(len(cuts)))+int(z>y)
            for w in extensions:
                groups[j][0]+=1
                groups[j][1]+=scores[tuple(sorted((z,)+w))]
        norm = n*(n-1)*comb(n-2, 2)
        for kk, dd in groups.values():
            kk=Q(kk,norm);dd=Q(dd,3*norm)
            features.extend([(dd, -kk) if full_near_optimality else
                             (dd-lower*kk, Q(0)), (-dd, kk)])
        rows.append(features)
    if degree_flag_weights:
        from near_optimal_weights import degree_flag_counts
        keys,counts,norm=degree_flag_counts(cover)
        for row,groups in zip(rows,counts):
            row.extend((-Q(groups.get(key,(0,0))[1],3*norm),
                         Q(groups.get(key,(0,0))[0],norm)) for key in keys)
    if weighted_thresholds:
        from near_optimal_weights import weighted_threshold_features
        extra=weighted_threshold_features(
            cover,lower,full_near_optimality=full_near_optimality)
        for row,additional in zip(rows,extra):row.extend(additional)
    return rows


def scalar_profile(cert):
    """Read optional constraint families without changing older certificates."""
    profile={key:cert.get(key,False) for key in
             ('full_near_optimality','degree_flag_weights','weighted_thresholds')}
    assert all(isinstance(value,bool) for value in profile.values())
    return profile


def verify_near(cover, cert):
    base = verify(cover, cert, return_values=True)
    scores = base.pop('values')
    lower = Q(cert['lower']); bar = Q(cert['bar'])
    assert 0 < lower < bar == Q(2, 3)
    if cover.get('field') == 'algebraic':
        from algebraic_field import make_field
        field = make_field(cover['polynomial'])
    elif cover.get('field') == 'cuberoot4':
        from cuberoot_field import F as field
    else:
        field = Q
    c = field(cover['c'])
    witness = cert['lower_witness']
    xs = list(map(Q, witness['support'])); masses = list(map(Q, witness['masses']))
    scale = Q(witness['scale_mass'])
    assert len(xs) == len(masses) and xs and min(xs) > 0
    assert min(masses) >= 0 and sum(masses) == 1 and 0 < scale < 1
    assert max(xs) < c*min(xs)
    beta = sum((masses[i]*masses[j]*masses[k]
                for i, j, k in product(range(len(xs)), repeat=3)
                if xs[i]+xs[j] < c*xs[k]), Q(0))
    witness_lower = (1-(1-beta)*scale**2)/(3-3*scale+scale**2)
    assert lower <= witness_lower
    multipliers = list(map(Q, cert['multipliers']))
    assert all(v >= 0 for v in multipliers)
    features = scalar_features(cover, lower, **scalar_profile(cert))
    at_lower = []; at_bar = []
    for value, row in zip(scores, features):
        assert len(row) == len(multipliers)
        intercept = value+sum(w*a for w, (a, b) in zip(multipliers, row))
        slope = sum(w*b for w, (a, b) in zip(multipliers, row))
        at_lower.append(intercept+lower*slope)
        at_bar.append(intercept+bar*slope)
    error = max(Q(0), max(at_lower)-lower)
    margin = bar-max(at_bar)
    assert margin > 0
    upper = lower+error*(bar-lower)/(margin+error)
    if 'upper' in cert:
        assert upper == Q(cert['upper'])
    base['flag_only_max'] = base.pop('exact_bound')
    base.pop('decimal')
    base.update(lower=str(lower), lower_witness_verified=True,
                witness_lower=str(witness_lower), max_at_lower=str(max(at_lower)),
                max_at_bar=str(max(at_bar)), margin=str(margin),
                upper=str(upper), upper_decimal=float(upper),
                gap_from_lower=float(upper-lower), scalar_coefficients_verified=True)
    return base


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('cover'); ap.add_argument('certificate')
    args = ap.parse_args()
    print(json.dumps(verify_near(read_json(args.cover), read_json(args.certificate)), indent=2))
