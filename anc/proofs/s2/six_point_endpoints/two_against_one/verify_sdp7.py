"""Independent exact evaluation of seven-point certificates.

Reconstructs flag products from signs and marked vertices; does not use the
SDP assembly, sparse operators, root_scores, or the numerical solver.
"""
import argparse
from fractions import Fraction as Q
from itertools import combinations
import json
from math import comb, lcm
from pathlib import Path
import sys

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'anton_endpoint'))
from enumerate_patterns import candidates, verify_cover


def verify(data, states, restrictions, certificate):
    if not data.get('complete'):
        raise ValueError('Incomplete six-point cover')
    verify_cover(data)
    if (certificate.get('format_version') not in (2, 3) or certificate.get('summands') != 2
            or certificate.get('s') != 7 or data['size'] != 6
            or data.get('summands') != 2
            or certificate['coefficient'] != data['coefficient']
            or certificate['tuples'] != data['tuples']):
        raise ValueError('Certificate/cover convention mismatch')
    patterns = np.array([[1 if s == '+' else -1 for s in row]
                         for row in data['patterns']], dtype=np.int8)
    lookup = {tuple(t): i for i, t in enumerate(data['tuples'])}
    cache = {}

    def induced(vertices):
        if vertices not in cache:
            indices = [lookup[tuple(vertices[i] for i in t)]
                       for t in candidates(len(vertices), False, 2)]
            cache[vertices] = [tuple(int(v) for v in row) for row in patterns[:, indices]]
        return cache[vertices]

    # Independently reconstruct the catalog numbering used by the archive.
    catalog, catalog_index, rows6 = [], {}, []
    fours6 = list(combinations(range(6), 4))
    signatures = [induced(four) for four in fours6]
    for column in range(len(patterns)):
        row = []
        for signature_list in signatures:
            signature = signature_list[column]
            if signature not in catalog_index:
                catalog_index[signature] = len(catalog)
                catalog.append(signature)
            row.append(catalog_index[signature])
        rows6.append(row)
    rows6 = np.array(rows6)
    if (states.ndim != 2 or states.shape[1] != 35 or len(states) == 0
            or restrictions.shape != (len(states), 7)
            or np.any(states < 0) or np.any(states >= len(catalog))
            or np.any(restrictions < 0) or np.any(restrictions >= len(patterns))
            or certificate['root_state_count'] != len(catalog)):
        raise ValueError('Invalid archive dimensions/indices')
    fours7 = list(combinations(range(7), 4))
    for j, six in enumerate(combinations(range(7), 6)):
        indices = [fours7.index(tuple(six[i] for i in q)) for q in fours6]
        if not np.array_equal(states[:, indices], rows6[restrictions[:, j]]):
            raise ValueError('Seven-point restriction mismatch')

    common6 = 60
    totals = np.array([row.count('+') for row in data['patterns']], dtype=object)
    for block in certificate['inherited']['blocks']:
        t, f = block['t'], block['f']
        if not 0 <= t < f <= 6 or 2*f-t > 6:
            raise ValueError('Invalid inherited dimensions')
        flags = {(tuple(signs), tuple(marks)): i
                 for i, (signs, marks) in enumerate(block['flags'])}
        if len(flags) != len(block['flags']):
            raise ValueError('Duplicate inherited flag')
        factor = [[Q(v) for v in row] for row in block['L']]
        if len(factor) != len(flags) or len({len(row) for row in factor}) != 1:
            raise ValueError('Invalid factor dimensions')
        d = lcm(*(v.denominator for row in factor for v in row))
        factor = [[int(v*d) for v in row] for row in factor]
        gram = np.array([[sum(a*b for a, b in zip(l, r)) for r in factor]
                         for l in factor], dtype=object)
        norm = comb(6, t)*comb(6-t, f-t)*comb(6-f, f-t)
        denominator = norm*d*d
        new_common = lcm(common6, denominator)
        totals *= new_common//common6
        common6 = new_common
        root_type = tuple(block['type'] or ())
        for roots in combinations(range(6), t):
            root_signs = induced(roots)
            rest = tuple(i for i in range(6) if i not in roots)
            for left_extra in combinations(rest, f-t):
                left = tuple(sorted(roots+left_extra))
                lm = tuple(left.index(i) for i in roots)
                left_indices = [flags.get((s, lm), -1) for s in induced(left)]
                for right_extra in combinations(tuple(i for i in rest if i not in left_extra), f-t):
                    right = tuple(sorted(roots+right_extra))
                    rm = tuple(right.index(i) for i in roots)
                    right_indices = [flags.get((s, rm), -1) for s in induced(right)]
                    columns = [i for i in range(len(patterns)) if root_signs[i] == root_type
                               and left_indices[i] >= 0 and right_indices[i] >= 0]
                    if columns:
                        a = [left_indices[i] for i in columns]
                        b = [right_indices[i] for i in columns]
                        totals[columns] += gram[a, b]*(common6//denominator)
    factor = certificate['root_factor']
    d = certificate['root_denominator']
    if (not isinstance(d, int) or d <= 0 or len(factor) != 4*len(catalog)
            or len({len(row) for row in factor}) != 1
            or any(type(v) is not int for row in factor for v in row)):
        raise ValueError('Invalid root factor')
    gram = np.array([[sum(a*b for a, b in zip(l, r)) for r in factor]
                     for l in factor], dtype=object)
    common = lcm(7*common6, 140*d*d)
    values = totals[restrictions].sum(axis=1)*(common//(7*common6))
    four_lookup = {v: i for i, v in enumerate(fours7)}
    for root in range(7):
        rest = tuple(i for i in range(7) if i != root)
        for extra in combinations(rest, 3):
            left = tuple(sorted((root,)+extra))
            right = tuple(sorted((root,)+tuple(i for i in rest if i not in extra)))
            a = states[:, four_lookup[left]].astype(np.int64)*4+left.index(root)
            b = states[:, four_lookup[right]].astype(np.int64)*4+right.index(root)
            values += gram[a, b]*(common//(140*d*d))
    if certificate['format_version'] == 3:
        # Reconstruct the extra products directly from marked subsets.
        # Do not import the numerical extra-block assembly or its operators.
        extra_cache = {}
        for block in certificate['extra_blocks']:
            t, f = block.get('t'), block.get('f')
            if (t, f) not in ((3, 5), (5, 6)) or block.get('encoding') != 1:
                raise ValueError('Unsupported extra flag block')
            width = len(candidates(f, False, 2))
            root_width = len(candidates(t, False, 2))
            mark_count = comb(f, t)
            flag_codes = block['flags']
            if (len(set(flag_codes)) != len(flag_codes) or not flag_codes
                    or any(type(v) is not int or not 0 <= v < (1 << width)*mark_count for v in flag_codes)
                    or type(block['root_code']) is not int or not 0 <= block['root_code'] < (1 << root_width)):
                raise ValueError('Invalid extra flag basis')
            factor, denominator = block['factor'], block['denominator']
            if (type(denominator) is not int or denominator <= 0 or len(factor) != len(flag_codes)
                    or len({len(row) for row in factor}) != 1
                    or any(type(v) is not int for row in factor for v in row)):
                raise ValueError('Invalid extra Gram factor')
            integer_factor = np.array(factor, dtype=object)
            gram = integer_factor @ integer_factor.T
            norm_den = comb(7, t)*comb(7-t, f-t)*comb(7-f, f-t)*denominator**2
            new_common = lcm(common, norm_den)
            values *= new_common//common
            common = new_common
            flags = {code: i for i, code in enumerate(flag_codes)}
            marks = list(combinations(range(f), t))

            def encoded(vertices):
                if vertices not in extra_cache:
                    # Obtain each comparison from any four-set containing
                    # its three vertices. Catalog signatures were rebuilt above.
                    result = np.zeros(len(states), dtype=np.int64)
                    local = list(candidates(4, False, 2))
                    for bit, event in enumerate(candidates(len(vertices), False, 2)):
                        triple = tuple(vertices[i] for i in event)
                        four = next(q for q in fours7 if set(triple) <= set(q))
                        position = local.index(tuple(four.index(i) for i in triple))
                        signs = np.array(catalog)[states[:, four_lookup[four]], position]
                        result += (signs == 1).astype(np.int64)*(1 << bit)
                    extra_cache[vertices] = result
                return extra_cache[vertices]

            for roots in combinations(range(7), t):
                selected = np.flatnonzero(encoded(roots) == block['root_code'])
                if not len(selected):
                    continue
                rest = tuple(i for i in range(7) if i not in roots)
                for left_extra in combinations(rest, f-t):
                    right_extra = tuple(i for i in rest if i not in left_extra)
                    left, right = tuple(sorted(roots+left_extra)), tuple(sorted(roots+right_extra))
                    lm = marks.index(tuple(left.index(i) for i in roots))
                    rm = marks.index(tuple(right.index(i) for i in roots))
                    a = np.array([flags.get(int(v)*mark_count+lm, -1) for v in encoded(left)[selected]])
                    b = np.array([flags.get(int(v)*mark_count+rm, -1) for v in encoded(right)[selected]])
                    keep = (a >= 0) & (b >= 0)
                    values[selected[keep]] += gram[a[keep], b[keep]]*(common//norm_den)
    bound = Q(int(max(values)), common)
    if bound != Q(certificate['exact_bound']):
        raise ValueError('Claimed bound differs from independent exact evaluation')
    return dict(exact_bound=str(bound), decimal_bound=float(bound),
                patterns_checked=len(states), independent_evaluation=True,
                coefficient=data['coefficient'],
                coverage='Conditional on complete seven-point archive; re-enumerate to check completeness')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6', type=Path, required=True)
    p.add_argument('--cover7', type=Path, required=True)
    p.add_argument('--certificate', type=Path, required=True)
    p.add_argument('--cover-seconds', type=float, default=300)
    args = p.parse_args()
    data = json.loads(args.cover6.read_text())
    archive = np.load(args.cover7)
    from sdp7 import enumerate_seven
    states, restrictions, rows6, report = enumerate_seven(
        data, seconds=args.cover_seconds, max_leaves=len(archive['states'])+1)
    if (not report['complete'] or not np.array_equal(states, archive['states'])
            or not np.array_equal(restrictions, archive['restrictions'])
            or not np.array_equal(rows6, archive['states6'])):
        raise ValueError('Archive failed complete compatibility re-enumeration')
    result = verify(data, archive['states'], archive['restrictions'],
                    json.loads(args.certificate.read_text()))
    result['complete_cover_reenumerated'] = True
    result['coverage'] = report['meaning']+'; complete cover re-enumerated'
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
