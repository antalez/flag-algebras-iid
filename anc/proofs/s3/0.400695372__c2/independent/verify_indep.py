"""Independent verifier for the n=4 ratio-coloured certificate.
Written from the definitions only (did not read verify.py / field_r.py / generators).

Conventions (inferred, tested by controls):
  pair form (i,j,c): f = x_j - q_c x_i ; sign '+'  <=> f < 0  (x_j < q x_i)
  sum form (a,b,c,d): f = x_a+x_b+x_c-2x_d ; '+' <=> f < 0 (win)
  Q(r) element [a0,a1,a2,a3] = a0+a1 r+a2 r^2+a3 r^3
  flag string: 9 chars = pairs (0,1),(0,2),(1,2) x cuts, roots = positions in sorted triple
"""
import json, sys, itertools, time
from fractions import Fraction as F
import qr

import os
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..') + os.sep


def load(coef_reverse=False, sumsign_flip=False, flagorder='pairmajor'):
    cover = json.load(open(D + 'cover_n4.json'))
    cert = json.load(open(D + 'cert_exact.json'))
    return cover, cert


PAIRS3 = [(0, 1), (0, 2), (1, 2)]


def parse_el(a, reverse=False):
    a = list(a)
    if reverse:
        a = a[::-1]
    return qr.make([F(x) for x in a])


class Setup:
    def __init__(self, cover, cert, reverse=False, flag_cutmajor=False):
        self.cuts = [F(c) for c in cover['cuts']]
        assert cover['cuts'] == cert['cuts'] and cover['form_order'] == cert['form_order']
        self.forms = cover['form_order']
        # index of pair form (i,j,c)
        self.pidx = {}
        for k, f in enumerate(self.forms):
            if f[0] == 'pair':
                self.pidx[(f[1], f[2], f[3])] = k
        self.sidx = {}
        for k, f in enumerate(self.forms):
            if f[0] == 'sum':
                self.sidx[tuple(f[1:])] = k
        # sanity: form list is exactly all 18 pair forms + the 2 sum forms
        assert sorted(self.pidx) == sorted((i, j, c) for i in range(4) for j in range(i + 1, 4) for c in range(3))
        assert set(self.sidx) == {(0, 1, 2, 3), (0, 1, 3, 2)}
        self.flag_cutmajor = flag_cutmajor
        self.blocks = []
        for b in cert['blocks']:
            assert b['t'] == 2 and b['f'] == 3
            flags = [(s, tuple(R)) for s, R in b['flags']]
            assert len(set(flags)) == len(flags), 'duplicate flags'
            W = [[parse_el(x, reverse) for x in row] for row in b['W']]
            Y = [[parse_el(x, reverse) for x in row] for row in b['Y']]
            self.blocks.append(dict(type=b['type'], flags=flags, idx={f: i for i, f in enumerate(flags)}, W=W, Y=Y))
        types = [b['type'] for b in self.blocks]
        assert len(set(types)) == len(types)
        self.btype = {b['type']: b for b in self.blocks}

    # ---- pattern restrictions
    def paircol(self, P, i, j):
        return ''.join(P[self.pidx[(i, j, c)]] for c in range(3))

    def flag_of(self, P, roots, x):
        pts = sorted(list(roots) + [x])
        if self.flag_cutmajor:
            s = ''.join(P[self.pidx[(pts[a], pts[b], c)]] for c in range(3) for (a, b) in PAIRS3)
        else:
            s = ''.join(self.paircol(P, pts[a], pts[b]) for (a, b) in PAIRS3)
        R = tuple(sorted(pts.index(r) for r in roots))
        return (s, R)

    def obj(self, P):
        w = (P[self.sidx[(0, 1, 2, 3)]] == '+') + (P[self.sidx[(0, 1, 3, 2)]] == '+')
        return F(w, 4)

    def flag_terms(self, P, Qs, missing=None):
        """sum_blocks <Q, M(P)>; M(P) = (1/12) sum over root pairs and ordered (c,d)."""
        tot = qr.ZERO
        for roots in itertools.combinations(range(4), 2):
            typ = self.paircol(P, *roots)
            others = [x for x in range(4) if x not in roots]
            if typ not in self.btype:
                if missing is not None:
                    missing.add(('type', typ))
                continue
            b = self.btype[typ]
            Q = Qs[typ]
            for c, d in [(others[0], others[1]), (others[1], others[0])]:
                f1 = self.flag_of(P, roots, c)
                f2 = self.flag_of(P, roots, d)
                assert f1[0][3 * PAIRS3.index(tuple(f1[1])) if False else 0] is not None
                if f1 not in b['idx'] or f2 not in b['idx']:
                    if missing is not None:
                        for f in (f1, f2):
                            if f not in b['idx']:
                                missing.add((typ, f))
                    continue
                tot = qr.add(tot, Q[b['idx'][f1]][b['idx'][f2]])
        return qr.scal(F(1, 12), tot)


def matmul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    assert len(A[0]) == m
    out = []
    for i in range(n):
        row = []
        for k in range(p):
            s = qr.ZERO
            for j in range(m):
                if any(A[i][j]) and any(B[j][k]):
                    s = qr.add(s, qr.mul(A[i][j], B[j][k]))
            row.append(s)
        out.append(row)
    return out


def transpose(A):
    return [list(x) for x in zip(*A)]


def ldl_posdef(Y):
    """Exact LDL^T over Q(r); returns list of pivots, asserts symmetric."""
    n = len(Y)
    for i in range(n):
        for j in range(n):
            assert Y[i][j] == Y[j][i], 'Y not symmetric'
    A = [row[:] for row in Y]
    piv = []
    for k in range(n):
        d = A[k][k]
        s = qr.sign(d)
        piv.append((s, qr.fval(d)))
        if s <= 0:
            return False, piv
        di = qr.inv(d)
        for i in range(k + 1, n):
            if not any(A[i][k]):
                continue
            l = qr.mul(A[i][k], di)
            for j in range(k + 1, n):
                if any(A[k][j]):
                    A[i][j] = qr.sub(A[i][j], qr.mul(l, A[k][j]))
    return True, piv


CBF = qr.scal(F(1, 4), qr.make([0, 6, -6, 1]))


def check_cbf():
    out = {}
    out['r'] = float(qr.rnum())
    out['CBF'] = qr.fval(CBF)
    # minimal polynomial 16y^4+8y^3+99y^2-32y-4 at y=CBF
    y = CBF
    y2 = qr.mul(y, y); y3 = qr.mul(y2, y); y4 = qr.mul(y3, y)
    val = qr.add(qr.add(qr.scal(16, y4), qr.scal(8, y3)), qr.add(qr.scal(99, y2), qr.add(qr.scal(-32, y), qr.scal(-4, qr.ONE))))
    out['minpoly_at_CBF_is_zero'] = (val == qr.ZERO)
    # numeric BF sup
    import numpy as np
    from scipy.optimize import minimize_scalar
    g = lambda p: -(p * (2 - p)) / (1 + p + p * p + p ** 3)
    res = minimize_scalar(g, bounds=(0, 1), method='bounded', options={'xatol': 1e-14})
    out['BF_sup_numeric'] = -res.fun
    out['BF_argmax_p'] = res.x
    return out


def build_Q(S):
    Qs = {}
    for b in S.blocks:
        W, Y = b['W'], b['Y']
        assert len(W) == len(b['flags']) and len(W[0]) == len(Y) == len(Y[0])
        Qs[b['type']] = matmul(matmul(W, Y), transpose(W))
    return Qs


def main(reverse=False, flag_cutmajor=False, verbose=True, cert_override=None, cover_override=None):
    cover, cert = load()
    if cert_override is not None:
        cert = cert_override
    if cover_override is not None:
        cover = cover_override
    S = Setup(cover, cert, reverse=reverse, flag_cutmajor=flag_cutmajor)
    res = {}
    # flags consistent with types
    bad = 0
    for b in S.blocks:
        for s, R in b['flags']:
            a, c = R
            pi = PAIRS3.index((a, c))
            if s[3 * pi:3 * pi + 3] != b['type']:
                bad += 1
    res['flags_inconsistent_with_type'] = bad
    # Y posdef
    pd = {}
    for b in S.blocks:
        ok, piv = ldl_posdef(b['Y'])
        pd[b['type']] = (ok, min(p[1] for p in piv), len(piv))
    res['Y_posdef'] = pd
    Qs = build_Q(S)
    missing = set()
    scores = []
    for P in cover['patterns']:
        assert len(P) == 20 and set(P) <= set('+-')
        ft = S.flag_terms(P, Qs, missing)
        sc = qr.add(qr.scal(S.obj(P), qr.ONE), ft)
        diff = qr.sub(CBF, sc)
        sg = qr.sign(diff)
        scores.append((P, S.obj(P), qr.fval(ft), qr.fval(sc), sg, qr.fval(diff)))
    res['n_patterns'] = len(scores)
    res['n_violations'] = sum(1 for s in scores if s[4] < 0)
    res['n_tight'] = sum(1 for s in scores if s[4] == 0)
    tight = sorted(s[0] for s in scores if s[4] == 0)
    res['tight_match_claim'] = (tight == sorted(cert['tight_patterns']))
    res['max_score'] = max(s[3] for s in scores)
    res['min_slack_nontight'] = min((s[5] for s in scores if s[4] > 0), default=None)
    res['worst_violation'] = min(s[5] for s in scores)
    res['missing_flags'] = len(missing)
    res['missing_examples'] = sorted(missing)[:10]
    if verbose:
        for k, v in res.items():
            print(k, v)
    return res, scores, S, Qs


if __name__ == '__main__':
    t = time.time()
    print('CBF check', check_cbf())
    res, scores, S, Qs = main()
    print('time', time.time() - t)
    json.dump([[s[0], str(s[1]), s[2], s[3], s[4], s[5]] for s in scores],
              open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'scores.json'), 'w'), indent=0)
