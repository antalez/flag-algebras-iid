"""Exact verifier, standard library only (fractions, itertools, json).

Checks for a cover + certificate:
  (1) the cover: every full sign vector lies in exactly one retained pattern or one excluded prefix, and
      every exclusion is a valid exact certificate (nonnegative nonzero weights, combination of the signed
      gap rows coordinatewise >= 0, contradicting strictness with positive gaps);
  (2) every block matrix is PSD (stage 2: Q = L L^T / D^2 with integer L, PSD by construction;
      stage 3: Q = W Y W^T over Q(r) with Y positive definite, checked by an exact LDL^T in Q(r));
  (3) obj(P) and M_sigma(P) are recomputed from the pattern definitions, and the exact score
      obj(P) + sum_sigma <Q_sigma, M_sigma(P)> is evaluated for every retained pattern.
No numerical solver is imported. Do not run with python -O (assertions are the checks).
"""
from fractions import Fraction as Fr
from itertools import combinations
from math import comb
import json, sys

N = 4
FAMILIES = {(0, 2), (1, 2), (2, 3)}


# ---------- definitions ----------
def canonical_forms(m, K):
    out = [('pair', i, j, q) for i, j in combinations(range(m), 2) for q in range(K)]
    for a, b, c, d in combinations(range(m), 4):
        out += [('sum', a, b, c, d), ('sum', a, b, d, c)]
    return out


def gap_rows(ff, cuts, zero, one):
    rows = []
    for f in ff:
        x = [zero] * N
        if f[0] == 'pair':
            _, i, j, q = f; x[j] = x[j] + one; x[i] = x[i] - cuts[q]
        else:
            _, a, b, c, d = f
            for v in (a, b, c): x[v] = x[v] + one
            x[d] = x[d] - 2 * one
        rows.append([sum(x[h:], zero) for h in range(N)])
    return rows


# ---------- enclosure of r and C_BF ----------
def poly_r(x):
    return x**4 - 4 * x**3 - 3 * x**2 - 2 * x + 2


def r_interval(bits):
    """Rational enclosure lo < r < hi of the root of r^4-4r^3-3r^2-2r+2 in (0,1), width 2^-bits.
    p(0)=2>0, p(1)=-6<0 and p'(x)=4x^3-12x^2-6x-2<0 on [0,1] (4x^3<=4x^2), so the root is unique."""
    lo, hi = Fr(0), Fr(1)
    assert poly_r(lo) > 0 > poly_r(hi)
    while hi - lo > Fr(1, 2**bits):
        mid = (lo + hi) / 2
        if poly_r(mid) > 0: lo = mid
        else: hi = mid
    assert poly_r(lo) > 0 > poly_r(hi)
    return lo, hi


def cbf_interval(bits=200):
    """C_BF = (r^3-6r^2+6r)/4 is increasing on [0, 0.58] (derivative (3r^2-12r+6)/4 > 0 for r < 2-sqrt2)."""
    lo, hi = r_interval(bits)
    assert 0 < lo and hi < Fr(58, 100)
    f = lambda x: (x**3 - 6 * x**2 + 6 * x) / 4
    return f(lo), f(hi)


# ---------- cover ----------
def check_cover(cover):
    cuts = [Fr(c) for c in cover['cuts']]
    assert all(c > 1 for c in cuts) and cuts == sorted(set(cuts))
    ff = [tuple(f) for f in cover['form_order']]
    assert ff == canonical_forms(N, len(cuts)), 'form order must be canonical'
    rows = gap_rows(ff, cuts, Fr(0), Fr(1))
    width = len(ff)
    ivals = []
    def interval(prefix):
        assert len(prefix) <= width and set(prefix) <= set('+-')
        start = int(''.join('1' if s == '+' else '0' for s in prefix) or '0', 2) << (width - len(prefix))
        return start, start + (1 << (width - len(prefix)))
    for prefix, w in cover['pruned'].items():
        w = {int(i): Fr(v) for i, v in w.items()}
        assert w and all(0 <= i < len(prefix) and v > 0 for i, v in w.items())
        for h in range(N):
            assert sum(v * (1 if prefix[i] == '+' else -1) * rows[i][h] for i, v in w.items()) >= 0
        ivals.append(interval(prefix))
    for p in cover['patterns']:
        assert len(p) == width; ivals.append(interval(p))
    end = 0
    for a, b in sorted(ivals):
        assert a == end, 'gap or overlap in the cover'
        end = b
    assert end == 1 << width
    return ff, cuts


# ---------- objective and moments from definitions ----------
def pattern_tools(ff, K):
    lookup = {f: i for i, f in enumerate(ff)}
    def subpat(P, verts):
        s = ''
        for f in canonical_forms(len(verts), K):
            if f[0] == 'pair':
                key = ('pair', verts[f[1]], verts[f[2]], f[3])
            else:
                key = ('sum',) + tuple(verts[v] for v in f[1:])
            s += P[lookup[key]]
        return s
    def obj(P):
        """P(X1+X2+X3<2X4) on a sorted 4-sample = (1/4) * #targets d with sum_{i!=d} x_i < 2 x_d.
        Targets 0,1 never win (x_2+x_3 > 2x_1 > ... ); target 3: form (0,1,2,3) '+', target 2: form (0,1,3,2) '+'."""
        wins = 0
        for d in range(N):
            if d < 2: continue
            others = tuple(i for i in range(N) if i != d)
            wins += P[lookup[('sum',) + others + (d,)]] == '+'
        return Fr(wins, 4)
    def flag_pairs(P, t, f, ty):
        """multiset of ordered (flagA, flagB): roots R with type ty, disjoint extensions A,B."""
        out = {}
        for R in combinations(range(N), t):
            if subpat(P, R) != ty: continue
            rest = [i for i in range(N) if i not in R]
            for ae in combinations(rest, f - t):
                a = tuple(sorted(R + ae)); fa = (subpat(P, a), tuple(a.index(i) for i in R))
                for be in combinations([i for i in rest if i not in ae], f - t):
                    b = tuple(sorted(R + be)); fb = (subpat(P, b), tuple(b.index(i) for i in R))
                    out[(fa, fb)] = out.get((fa, fb), 0) + 1
        return out
    return obj, flag_pairs


# ---------- PSD checks ----------
def gram_from_L(L):
    assert len(set(map(len, L))) <= 1 and all(type(v) == int for row in L for v in row)
    d = len(L)
    return [[sum(a * b for a, b in zip(L[i], L[j])) for j in range(d)] for i in range(d)]


def ldl_positive_definite(Y, zero):
    """exact LDL^T; True iff every pivot > 0 (sign decided exactly by the number type)."""
    d = len(Y); A = [list(r) for r in Y]
    for i in range(d):
        for j in range(d): assert A[i][j] == A[j][i], 'Y not symmetric'
    for k in range(d):
        p = A[k][k]
        if not (p > zero): return False
        for i in range(k + 1, d):
            if A[i][k] == zero: continue
            f = A[i][k] / p
            for j in range(k + 1, d): A[i][j] = A[i][j] - f * A[k][j]
            A[i][k] = zero
    return True


# ---------- main check ----------
def verify(cover, cert, field=None):
    ff, cuts = check_cover(cover)
    assert [Fr(c) for c in cert['cuts']] == cuts and [tuple(f) for f in cert['form_order']] == ff
    K = len(cuts)
    obj, flag_pairs = pattern_tools(ff, K)
    seen = set()
    blocks = []
    for B in cert['blocks']:
        t, f, ty = B['t'], B['f'], B['type']
        assert (t, f) in FAMILIES and len(ty) == len(canonical_forms(t, K)) and set(ty) <= set('+-')
        flags = [(a, tuple(b)) for a, b in B['flags']]
        assert len(set(flags)) == len(flags)
        idx = {fl: i for i, fl in enumerate(flags)}
        norm = comb(N, t) * comb(N - t, f - t) * comb(N - f, f - t)
        if cert['kind'] == 'rational_gram':
            G = gram_from_L(B['L']); assert len(G) == len(flags) and B['D'] > 0
            Qm = [[Fr(v, B['D'] ** 2) for v in row] for row in G]     # PSD: L L^T
        else:
            Qm = field_block(B, field, len(flags))
        blocks.append((t, f, ty, idx, norm, Qm))
    scores = []
    for P in cover['patterns']:
        s = obj(P)
        for t, f, ty, idx, norm, Qm in blocks:
            acc = Fr(0) if field is None else field.zero     # exact zero (an int 0 / norm would be a float)
            for (a, b), c in flag_pairs(P, t, f, ty).items():
                if a in idx and b in idx:            # flags missing from the list are zero coordinates
                    acc = acc + c * Qm[idx[a]][idx[b]]
            s = s + acc / norm
        assert isinstance(s, Fr) if field is None else type(s) is type(field.zero), 'inexact score type'
        scores.append(s)
    return scores


def field_block(B, F, d):
    """Q = W Y W^T over Q(r); W given as d x k, Y as k x k (k x k positive definite, checked exactly)."""
    W = [[F.parse(v) for v in row] for row in B['W']]
    Y = [[F.parse(v) for v in row] for row in B['Y']]
    k = len(Y); assert len(W) == d and all(len(row) == k for row in W)
    assert ldl_positive_definite(Y, F.zero), 'Y not positive definite'
    WY = [[sum((W[i][a] * Y[a][b] for a in range(k)), F.zero) for b in range(k)] for i in range(d)]
    return [[sum((WY[i][b] * W[j][b] for b in range(k)), F.zero) for j in range(d)] for i in range(d)]


def stage2_report(cover, cert):
    scores = verify(cover, cert)
    bound = max(scores)
    if 'bound' in cert: assert Fr(cert['bound']) == bound, 'claimed bound differs from recomputed bound'
    lo, hi = cbf_interval()
    assert bound >= lo, 'bound below C_BF: impossible (contradicts the BF lower bound), certificate is wrong'
    return dict(bound=str(bound), bound_float=float(bound), patterns=len(scores),
                exclusions=len(cover['pruned']), blocks=[len(B['flags']) for B in cert['blocks']],
                excess_over_CBF_upper=float(bound - lo), excess_over_CBF_lower=float(bound - hi),
                CBF_enclosure_width=float(hi - lo))


def stage3_report(cover, cert):
    """Exact check over K = Q(r): every retained pattern has score <= C_BF = (r^3-6r^2+6r)/4."""
    from field_r import Field, K, R
    assert cert['kind'] == 'field_face'
    cbf = (R**3 - 6 * R**2 + 6 * R) / 4
    assert R**4 - 4 * R**3 - 3 * R**2 - 2 * R + 2 == 0 and K(0) < R < K(1)
    scores = verify(cover, cert, field=Field)
    slack = [cbf - s for s in scores]
    signs = [x.sign() for x in slack]
    assert all(sg >= 0 for sg in signs), 'some pattern scores above C_BF'
    tight = [p for p, sg in zip(cover['patterns'], signs) if sg == 0]
    if 'tight_patterns' in cert: assert sorted(tight) == sorted(cert['tight_patterns'])
    pos = [float(x) for x, sg in zip(slack, signs) if sg > 0]
    return dict(result='every retained pattern: obj(P) + sum <Q_s, M_s(P)> <= C_BF exactly (Q_s = W Y W^T, Y positive definite)',
                patterns=len(scores), exclusions=len(cover['pruned']), tight_exact_zero_slack=len(tight),
                min_positive_slack=min(pos), blocks=[(B['t'], B['f'], B['type'], len(B['flags']), len(B['Y'])) for B in cert['blocks']])


if __name__ == '__main__':
    cover = json.load(open(sys.argv[1])); cert = json.load(open(sys.argv[2]))
    if cert['kind'] == 'rational_gram':
        print(json.dumps(stage2_report(cover, cert), indent=1))
    else:
        print(json.dumps(stage3_report(cover, cert), indent=1))
