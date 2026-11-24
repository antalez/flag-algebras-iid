"""Exact verifier for the order-seven flag certificate of sup P(X1+X2+X3 < (1+sqrt 2) X4).

Adapted from ../verify7_full.py (c = 2).  Inputs
  farkas_k_excluded.json   for s = 5, 6, 7: exact non-realizability certificates over Q(sqrt 2)
  cert7_full_k.json        flags and integer factors L of the PSD matrices Q = L L^T / 4^scale_bits

Checked in exact arithmetic (integers and Q(sqrt 2); NumPy only batches exact integer operations):
  1. the s-point cover is the join of the surviving (s-1)-point patterns, s = 5, 6, 7, starting from
     all four states at s = 4; so every realizable seven-point pattern survives;
  2. each excluded cover pattern carries a valid certificate (positive Q(sqrt 2) combination of its own
     strict inequalities that is coordinatewise >= 0); kappa enters only here, exactly;
  3. for every remaining pattern P:  c(P) + sum_b <Q_b, M_b(P)>  is computed exactly; the maximum is the bound.
No code is shared with the optimiser (patterns_k.py, flags.py, ipm.py, certify7_k.py).
"""
import argparse
import gzip
import itertools as it
import json
import math
import sys
import time
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

import numpy as np


def require(cond, msg):
    if not cond:
        raise ValueError(msg)


def join_level(states_lower, s):
    """All s-point state vectors whose (s-1)-point restrictions are all in `states_lower` (2 bits per 4-subset)."""
    fours_l = list(it.combinations(range(s - 1), 4))
    index = {q: j for j, q in enumerate(it.combinations(range(s), 4))}
    n4 = len(index)
    joined, known = [0], 0
    for subset in it.combinations(range(s), s - 1):
        scope = [index[tuple(subset[j] for j in four)] for four in fours_l]
        mask = sum(3 << (2 * j) for j in scope)
        overlap, fresh = known & mask, mask & ~known
        table = defaultdict(list)
        for st in states_lower:
            code = sum(v << (2 * j) for v, j in zip(st, scope))
            table[code & overlap].append(code & fresh)
        joined = [old | extra for old in joined for extra in table[old & overlap]]
        known |= mask
    require(known == (1 << (2 * n4)) - 1 and len(set(joined)) == len(joined), 'bad join')
    states = np.empty((len(joined), n4), dtype=np.int64)
    for j in range(n4):
        states[:, j] = [(code >> (2 * j)) & 3 for code in joined]
    return states


def linear_forms(s):
    """Form k of a 4-subset a<b<c<d, target t_k = (d, c, b)[k]: (sum of the other three x) - kappa x_t,
    kappa = 1 + sqrt(2), in gap coordinates as an exact pair (U, V): U + sqrt(2) V."""
    def x(i):
        return [1 if g <= i else 0 for g in range(s)]
    forms = []
    for a, b, c, d in it.combinations(range(s), 4):
        row = []
        for t in (d, c, b):
            others = [v for v in (a, b, c, d) if v != t]
            U = [sum(x(o)[g] for o in others) - x(t)[g] for g in range(s)]
            V = [-x(t)[g] for g in range(s)]
            row.append((U, V))
        forms.append(row)
    return forms


def nonneg(a, b):
    """a + b sqrt(2) >= 0, integers a, b."""
    if a >= 0 and b >= 0:
        return True
    if a < 0 and b < 0:
        return False
    return a * a >= 2 * b * b if a >= 0 else 2 * b * b >= a * a


def check_exclusions(cover, data, s):
    """Remove the cover patterns carrying a valid exclusion certificate.

    Entry (j, k, sg, p, q): weight p + sqrt(2) q (p, q >= 0 integers, not both 0) on the strict inequality
    sg * F_k(j) < 0 implied by the pattern: sg = +1 needs state >= k+1 (target t_k succeeds), sg = -1 needs
    state <= k (target t_k fails; strict since ties are excluded as in the c = 2 case).
    Valid if sum of weight * (sg F_k) is coordinatewise >= 0 in Q(sqrt 2): impossible for gaps d >= 0, d != 0."""
    forms = linear_forms(s)
    cover_set = {tuple(int(v) for v in row) for row in cover}
    excluded = set()
    for states, cert in zip(data['excluded'], data['certificates']):
        states = tuple(states)
        require(states in cover_set and states not in excluded, 'excluded pattern not in cover or repeated')
        require(len(cert) > 0, 'empty certificate')
        ta, tb = [0] * s, [0] * s
        for j, k, sg, p, q in cert:
            require(all(isinstance(v, int) for v in (j, k, sg, p, q)), 'non-integer entry')
            require(p >= 0 and q >= 0 and p + q > 0, 'bad weight')
            require(0 <= k <= 2 and sg in (1, -1), 'bad form')
            st = states[j]
            require(st >= k + 1 if sg == 1 else st <= k, 'inequality not implied by the pattern')
            U, V = forms[j][k]
            for g in range(s):
                u, v = sg * U[g], sg * V[g]
                ta[g] += p * u + 2 * q * v          # (p + q r)(u + v r), r^2 = 2
                tb[g] += p * v + q * u
        require(all(nonneg(a, b) for a, b in zip(ta, tb)), 'invalid exclusion certificate')
        excluded.add(states)
    keep = np.array([tuple(int(v) for v in row) not in excluded for row in cover])
    return cover[keep], len(excluded)


def induced_code(P, subset, index):
    """Base-4 code of the pattern induced on `subset` (and its state columns)."""
    f = len(subset)
    cols = [index[tuple(subset[i] for i in q)] for q in it.combinations(range(f), 4)]
    code = np.zeros(len(P), dtype=np.int64)
    for k, c in enumerate(cols):
        code += P[:, c] * 4 ** k
    return code


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parent
    ap.add_argument('--certificate', type=Path, default=here / 'cert7_full_k.json.gz')
    ap.add_argument('--exclusions', type=Path, default=here / 'farkas_k_excluded.json.gz')
    args = ap.parse_args()
    require(not sys.flags.optimize, 'run without -O')
    t0 = time.time()
    s = 7
    with (gzip.open(args.exclusions, 'rt') if args.exclusions.suffix == '.gz'
          else args.exclusions.open()) as stream:
        excl = json.load(stream)
    P = np.arange(4, dtype=np.int64)[:, None]                 # s = 4: all four states
    for level in (5, 6, 7):
        cover = join_level([tuple(int(v) for v in row) for row in P], level)
        P, nex = check_exclusions(cover, excl[str(level)], level)
        print(f'{level}-point cover: {len(cover)}; excluded with exact Q(sqrt2) certificates: {nex}; '
              f'remaining {len(P)}  [{time.time()-t0:.0f}s]', flush=True)
    N = len(P)
    print(f'excluded with exact certificates: {nex}; remaining patterns: {N}  [{time.time()-t0:.0f}s]', flush=True)

    with (gzip.open(args.certificate, 'rt') if args.certificate.suffix == '.gz'
          else args.certificate.open()) as stream:
        cert = json.load(stream)
    require(cert['s'] == 7, 'wrong certificate size')
    require(cert.get('kappa') == '1+sqrt(2)', 'certificate is not for kappa = 1+sqrt(2)')
    K = int(cert['scale_bits'])
    index = {q: j for j, q in enumerate(it.combinations(range(s), 4))}
    DEN = 1260
    total = P.sum(axis=1).astype(object) * (DEN // 140) * (1 << (2 * K))      # c(P) = (#successes)/140

    families = defaultdict(list)
    for b in cert['blocks']:
        families[(b['t'], b['f'])].append(b)
    for (t, f), blocks in sorted(families.items()):
        require(0 < t < f and 2 * f - t <= s, 'unsupported family')
        n4 = math.comb(f, 4)
        flagmap = {}                       # (code of f-pattern, root positions) -> global row id
        grams, base = [], 0
        for b in blocks:
            L = np.array([[int(v) for v in row] for row in b['L']], dtype=object)
            require(L.shape[0] == len(b['flags']), 'factor shape')
            G = L.dot(L.T)                 # exact integer Gram matrix (PSD by construction)
            for r, (st, roots) in enumerate(b['flags']):
                require(len(st) == n4 and all(v in (0, 1, 2, 3) for v in st), 'bad flag pattern')
                require(len(roots) == t and list(roots) == sorted(set(roots)) and all(0 <= v < f for v in roots), 'bad roots')
                # the declared type must be the pattern induced on the roots
                if t >= 4:
                    sub = {q: j for j, q in enumerate(it.combinations(range(f), 4))}
                    ty = [st[sub[tuple(roots[i] for i in q)]] for q in it.combinations(range(t), 4)]
                    require(ty == b['type'], 'flag does not have the block type')
                key = (sum(v * 4 ** k for k, v in enumerate(st)), tuple(roots))
                require(key not in flagmap, 'duplicate flag')
                flagmap[key] = (len(grams), r)
            grams.append(G)
        # dense lookup tables: code -> small id
        codes = sorted({k[0] for k in flagmap})
        code_id = {c: i for i, c in enumerate(codes)}
        rootsets = list(it.combinations(range(f), t))
        blk = np.full((len(codes) + 1, len(rootsets)), -1, dtype=np.int64)
        row = np.full((len(codes) + 1, len(rootsets)), -1, dtype=np.int64)
        for (c, roots), (bi, r) in flagmap.items():
            blk[code_id[c], rootsets.index(roots)] = bi
            row[code_id[c], rootsets.index(roots)] = r
        sorted_codes = np.array(codes, dtype=np.int64)
        norm = math.comb(s, t) * math.comb(s - t, f - t) * math.comb(s - f, f - t)   # ordered (S, A, B)
        require(DEN % norm == 0 or (2 * DEN) % norm == 0, 'normalisation')
        fam_sum = np.zeros(N, dtype=object)
        cache = {}

        def flag_ids(U, S):
            if U not in cache:
                code = induced_code(P, U, index)
                pos = np.searchsorted(sorted_codes, code)
                pos = np.minimum(pos, len(sorted_codes) - 1)
                cache[U] = np.where(sorted_codes[pos] == code, pos, len(codes))    # missing -> dummy row of -1
            ri = rootsets.index(tuple(U.index(v) for v in S))
            return blk[cache[U], ri], row[cache[U], ri]

        for S in it.combinations(range(s), t):
            rest = [v for v in range(s) if v not in S]
            ext = list(it.combinations(rest, f - t))
            ids = {A: flag_ids(tuple(sorted(S + A)), S) for A in ext}
            for A in ext:
                for B in ext:
                    if set(A) & set(B):
                        continue                       # ordered pairs of disjoint extensions
                    (b1, r1), (b2, r2) = ids[A], ids[B]
                    ok = (b1 >= 0) & (b2 >= 0)
                    require(bool(np.all(b1[ok] == b2[ok])), 'two flags on the same roots lie in different blocks')
                    for bi in np.unique(b1[ok]):
                        sel = np.flatnonzero(ok & (b1 == bi))
                        fam_sum[sel] += grams[bi][r1[sel], r2[sel]]
        require((DEN * fam_sum[0]) % norm == 0 or True, '')
        # value contribution = fam_sum / (norm * 4^K); common denominator DEN * 4^K with DEN/norm possibly fractional
        fr = Fraction(DEN, norm)
        require(all((int(v) * fr.numerator) % fr.denominator == 0 for v in fam_sum[:50]), 'non-integral contribution')
        total += np.array([int(v) * fr.numerator // fr.denominator for v in fam_sum], dtype=object)
        require(all((int(v) * fr.numerator) % fr.denominator == 0 for v in fam_sum), 'non-integral contribution')
        print(f'family (t={t}, f={f}): {len(blocks)} blocks, {len(flagmap)} flags  [{time.time()-t0:.0f}s]', flush=True)

    bound = Fraction(int(max(total)), DEN * (1 << (2 * K)))
    print(f'CERTIFIED: C <= {bound.numerator}/{bound.denominator}  ~= {float(bound):.16f}')
    claimed = Fraction(int(cert['claimed_bound'][0]), int(cert['claimed_bound'][1]))
    print('matches the claimed bound:', bound == claimed)
    require(bound == claimed == Fraction(96556198460261613624314242853,
                                         194975556187447393296612065280),
            'computed bound differs from the manuscript bound')


if __name__ == '__main__':
    main()
