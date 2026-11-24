"""Reconstruct and verify pattern exclusions at the exact algebraic c4.

Weights are integer polynomials in c. Their signs at c4 are proved by
reduction modulo c^5-c^3-c^2-c-2 and rational interval arithmetic.
No floating-point sign or infeasibility decision is accepted as a proof.
"""
import argparse
from fractions import Fraction as Q
from math import factorial, gcd, lcm
import json
from pathlib import Path
import time

from sdp7 import candidates, save

POLY = [-2, -1, -1, -1, 0, 1]


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p or [0]


def add(p, q):
    r = [0]*max(len(p), len(q))
    for i, v in enumerate(p):
        r[i] += v
    for i, v in enumerate(q):
        r[i] += v
    return trim(r)


def linear_product(p, a, b):
    r = [0]*(len(p)+1)
    for i, v in enumerate(p):
        r[i] += a*v
        r[i+1] += b*v
    return trim(r)


def divide(p, polynomial=POLY):
    """Integer quotient and remainder by the monic endpoint polynomial."""
    r = trim(p)
    degree = len(polynomial)-1
    quotient = [0]*max(1, len(r)-degree)
    while len(r) > degree:
        j, value = len(r)-degree-1, r[-1]
        quotient[j] = value
        for k, coefficient in enumerate(polynomial):
            r[j+k] -= value*coefficient
        r = trim(r)
    return trim(quotient), r


def isolate(bits=256, polynomial=POLY):
    denominator = 1 << bits
    lo, hi = denominator, 2*denominator

    def value(x):
        return sum(v*x**j*denominator**(len(polynomial)-1-j) for j, v in enumerate(polynomial))

    while hi-lo > 1:
        mid = (lo+hi)//2
        if value(mid) > 0:
            hi = mid
        else:
            lo = mid
    if not value(lo) < 0 < value(hi):
        raise ValueError('Invalid isolating interval')
    return lo, hi, denominator


def sign_at_root(p, interval, polynomial=POLY):
    _, p = divide(p, polynomial)
    if not any(p):
        return 0
    lo, hi, den = interval
    lower = upper = p[-1]*den
    for coefficient in reversed(p[:-1]):
        products = (lower*lo, lower*hi, upper*lo, upper*hi)
        lower = min(products)//den+coefficient*den
        upper = -((-max(products))//den)+coefficient*den
    if lower > 0:
        return 1
    if upper < 0:
        return -1
    raise ValueError('Polynomial sign unresolved by the isolating interval')


def determinant(a):
    """Integer determinant by fraction-free elimination, including pivots."""
    n = len(a)
    if not n:
        return 1
    a = [list(row) for row in a]
    previous, orientation = 1, 1
    for k in range(n-1):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            orientation = -orientation
        value = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                q, r = divmod(value*a[i][j]-a[i][k]*a[k][j], previous)
                if r:
                    raise ValueError('Nonintegral determinant elimination')
                a[i][j] = q
            a[i][k] = 0
        previous = value
    return orientation*a[-1][-1]


def determinant_polynomial(matrix):
    """d! times det(A+c B), from exact integer Newton interpolation."""
    d = len(matrix)
    differences = [determinant([[a+b*c for a, b in row] for row in matrix])
                   for c in range(d+1)]
    result, falling = [0], [1]
    for j in range(d+1):
        coefficient = differences[0]*(factorial(d)//factorial(j))
        result = add(result, [coefficient*v for v in falling])
        differences = [b-a for a, b in zip(differences, differences[1:])]
        falling = linear_product(falling, -j, 1)
    return trim(result)


def rows_for(n, indices, signs):
    events = candidates(n, False, 2)
    return [[(sign*sum(i >= j for i in events[index][:-1]),
              -sign*int(events[index][-1] >= j)) for j in range(n)]
            for index, sign in zip(indices, signs)]


def verify_ray(proof, interval, polynomial=POLY):
    n, ids, signs, weights = proof['size'], proof['events'], proof['signs'], proof['weights']
    if (n not in (6, 7) or not ids or len(set(ids)) != len(ids)
            or len(ids) != len(signs) or len(ids) != len(weights)
            or any(type(i) is not int or not 0 <= i < len(candidates(n, False, 2)) for i in ids)
            or any(s not in (-1, 1) for s in signs)
            or any(not p or any(type(v) is not int for v in p) for p in weights)):
        raise ValueError('Invalid algebraic Farkas proof')
    wsigns = [sign_at_root(w, interval, polynomial) for w in weights]
    if min(wsigns) < 0 or max(wsigns) <= 0:
        raise ValueError('Weights are not nonnegative and nonzero at the endpoint')
    rows = rows_for(n, ids, signs)
    for j in range(n):
        value = [0]
        for w, row in zip(weights, rows):
            value = add(value, linear_product(w, *row[j]))
        if sign_at_root(value, interval, polynomial) < 0:
            raise ValueError('Negative algebraic Farkas slack')
    return True


def reconstruct(n, pattern, encoded, coefficient, interval, tolerance=Q(0), polynomial=POLY):
    ids = sorted(map(int, encoded))
    signs = [1 if pattern[i] == '+' else -1 for i in ids]
    if any(Q(encoded[str(i)][1]) for i in ids):
        raise ValueError('Expected rational seed weights')
    fractions = [Q(encoded[str(i)][0]) for i in ids]
    den = lcm(*(w.denominator for w in fractions))
    ws = [int(w*den) for w in fractions]
    rows = rows_for(n, ids, signs)
    p, q = coefficient.numerator, coefficient.denominator
    slacks = [sum(w*(row[j][0]*q+row[j][1]*p) for w, row in zip(ws, rows))
              for j in range(n)]
    # Simple rational seed rays can have tiny positive residuals where the
    # original LP ray has a zero slack. Try those columns as exact equations;
    # acceptance still depends entirely on the algebraic sign checks below.
    zero_columns = sorted((j for j in range(n) if abs(slacks[j]) <= tolerance*sum(ws)*q),
                          key=lambda j: abs(slacks[j]))
    proposals = [[row[j] for row in rows] for j in zero_columns]
    for j in range(1, len(ids)):
        row = [(0, 0)]*len(ids)
        row[0], row[j] = (-ws[j], 0), (ws[0], 0)
        proposals.append(row)
    basis, equations = [], []
    for row in proposals:
        values = [a*q+b*p for a, b in row]
        for pivot, old in basis:
            if values[pivot]:
                values = [old[pivot]*a-values[pivot]*b for a, b in zip(values, old)]
                common = gcd(*values)
                if common:
                    values = [v//common for v in values]
        pivot = next((i for i, v in enumerate(values) if v), None)
        if pivot is not None:
            common = gcd(*values)
            values = [v//common for v in values]
            basis.append((pivot, values))
            equations.append(row)
        if len(equations) == len(ids)-1:
            break
    if len(equations) != len(ids)-1:
        raise ValueError('Could not select cofactor equations')
    weights = []
    for i in range(len(ids)):
        minor = [[v for j, v in enumerate(row) if j != i] for row in equations]
        weights.append([(-1)**i*v for v in determinant_polynomial(minor)])
    # At an algebraic endpoint every cofactor can share the minimal
    # polynomial. Cancel that common factor before taking endpoint signs.
    while all(not any(divide(w, polynomial)[1]) for w in weights):
        if not any(any(w) for w in weights):
            raise ValueError('Identically zero cofactor vector')
        weights = [divide(w, polynomial)[0] for w in weights]
    common = gcd(*(v for w in weights for v in w))
    if common:
        weights = [[v//common for v in w] for w in weights]
    sig = [sign_at_root(w, interval, polynomial) for w in weights]
    if max(sig) <= 0:
        weights = [[-v for v in w] for w in weights]
    proof = dict(size=n, events=ids, signs=signs, weights=weights)
    verify_ray(proof, interval, polynomial)
    return proof



def reconstruct_with_alternatives(n, pattern, encoded, coefficient, interval, polynomial=POLY):
    """Reconstruct a seed ray, then try different LP supports if necessary.

    Floating-point LPs only propose weights and supports. Every accepted ray
    passes verify_ray at the algebraic endpoint with exact arithmetic.
    """
    tolerances = (Q(0), Q(1, 10**6), Q(1, 10**4))
    last = None
    for tolerance in tolerances:
        try:
            return reconstruct(n, pattern, encoded, coefficient, interval, tolerance, polynomial)
        except ValueError as exc:
            last = exc
    import highspy
    import numpy as np
    rows = rows_for(n, range(len(pattern)), [1 if v == '+' else -1 for v in pattern])
    lo, hi, den = interval
    for c in dict.fromkeys((float(coefficient), (lo+hi)/(2*den))):
        for feasibility_tolerance in (1e-9, 1e-7):
            h = highspy.Highs()
            for key, value in [('output_flag', False), ('presolve', 'off'), ('solver', 'simplex'),
                               ('primal_feasibility_tolerance', feasibility_tolerance),
                               ('dual_feasibility_tolerance', feasibility_tolerance)]:
                h.setOptionValue(key, value)
            h.addCols(n, np.ones(n), np.zeros(n), np.full(n, highspy.kHighsInf), 0,
                      np.zeros(n+1, dtype=np.int32), np.array([], dtype=np.int32), np.array([]))
            m = len(rows)
            a = np.array([[x+y*c for x, y in row] for row in rows])
            h.addRows(m, np.full(m, -highspy.kHighsInf), np.full(m, -1.), m*n,
                      np.arange(0, (m+1)*n, n, dtype=np.int32),
                      np.tile(np.arange(n, dtype=np.int32), m), a.ravel())
            if h.run() == highspy.HighsStatus.kError:
                continue
            _, exists, dual = h.getDualRay()
            if not exists:
                continue
            weights = -np.asarray(dual)
            scale = max(abs(weights))
            if not scale:
                continue
            seed = {str(i): [str(Q(float(w/scale)).limit_denominator(10**6)), '0']
                    for i, w in enumerate(weights) if w > scale*1e-10}
            if not seed:
                continue
            for tolerance in tolerances:
                try:
                    return reconstruct(n, pattern, seed, Q(str(c)), interval, tolerance, polynomial)
                except ValueError as exc:
                    last = exc
    raise ValueError(str(last) if last else 'No exact endpoint ray found')


def verify_endpoint(data, proof, polynomial=POLY):
    from enumerate_patterns import verify_cover
    if not data.get('complete') or data.get('size') != 6 or data.get('summands') != 2:
        raise ValueError('Expected a complete two-summand six-point cover')
    # The verified binary partition is coefficient-independent. Replace each
    # excluded prefix's rational ray by its algebraic endpoint ray below.
    verify_cover(data)
    if proof['polynomial'] != polynomial:
        raise ValueError('Wrong endpoint polynomial')
    interval = tuple(map(int, proof['interval']))
    lo, hi, den = interval
    if (den <= 0 or not den < lo < hi < 2*den or
            not sum(v*lo**j*den**(len(polynomial)-1-j) for j, v in enumerate(polynomial)) < 0 <
                sum(v*hi**j*den**(len(polynomial)-1-j) for j, v in enumerate(polynomial))):
        raise ValueError('Invalid root isolation')
    for ray in proof['rays']:
        verify_ray(ray, interval, polynomial)
    for key, n in [('pruned', 6), ('seven_exclusions', 7)]:
        if set(proof[key]) != set(data.get(key, {})):
            raise ValueError('Endpoint coverage omits an exclusion')
        for pattern, index in proof[key].items():
            if type(index) is not int or not 0 <= index < len(proof['rays']):
                raise ValueError('Invalid ray reference')
            ray = proof['rays'][index]
            if ray['size'] != n or any(i >= len(pattern) or pattern[i] != ('+' if s == 1 else '-')
                for i, s in zip(ray['events'], ray['signs'])):
                raise ValueError('Endpoint ray belongs to a different pattern')
    return dict(exact_endpoint_cover=True, six_exclusions=len(proof['pruned']),
                seven_exclusions=len(proof['seven_exclusions']), rays=len(proof['rays']))


def main(polynomial=POLY):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--verify', action='store_true')
    p.add_argument('--polynomial', type=int, nargs='+',
                   help='Override the monic endpoint polynomial, constant coefficient first')
    args = p.parse_args()
    if args.polynomial is not None:
        polynomial = args.polynomial
        if len(polynomial) < 2 or polynomial[-1] != 1:
            p.error('Require a nonconstant monic polynomial')
    data = json.loads(args.cover6.read_text())
    if args.verify:
        print(json.dumps(verify_endpoint(data, json.loads(args.output.read_text()), polynomial)), flush=True)
        return
    interval = isolate(polynomial=polynomial)
    output = dict(polynomial=polynomial, interval=list(map(str, interval)), rays=[],
                  pruned={}, seven_exclusions={}, failures=[])
    cache = {}
    coefficient = Q(data['coefficient'][0])
    tick = last = time.monotonic()
    for key, n in [('pruned', 6), ('seven_exclusions', 7)]:
        for pattern, encoded in data.get(key, {}).items():
            signature = (n, tuple((int(i), pattern[int(i)], tuple(v))
                                 for i, v in sorted(encoded.items(), key=lambda item: int(item[0]))))
            if signature in cache and cache[signature] is not None:
                ray = output['rays'][cache[signature]]
                # Alternative supports can use events absent from the seed
                # signature. Reuse only if every such sign matches this branch.
                if any(i >= len(pattern) or pattern[i] != ('+' if v == 1 else '-')
                       for i, v in zip(ray['events'], ray['signs'])):
                    signature = (signature, pattern)
            if signature not in cache:
                try:
                    ray = reconstruct_with_alternatives(n, pattern, encoded, coefficient, interval, polynomial)
                    cache[signature] = len(output['rays'])
                    output['rays'].append(ray)
                except ValueError as exc:
                    cache[signature] = None
                    output['failures'].append(dict(size=n, pattern=pattern, reason=str(exc)))
            index = cache[signature]
            if index is not None:
                output[key][pattern] = index
            if time.monotonic()-last > 20:
                save(args.output, output)
                print(json.dumps(dict(six=len(output['pruned']), seven=len(output['seven_exclusions']),
                    rays=len(output['rays']), failures=len(output['failures']), seconds=time.monotonic()-tick)), flush=True)
                last = time.monotonic()
    output['complete'] = not output['failures']
    save(args.output, output)
    if output['complete']:
        print(json.dumps(verify_endpoint(data, output, polynomial)), flush=True)
    else:
        print(json.dumps(dict(complete=False, failures=len(output['failures']), examples=output['failures'][:5])), flush=True)


if __name__ == '__main__':
    main()
