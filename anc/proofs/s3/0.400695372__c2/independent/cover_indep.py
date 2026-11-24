"""Independent cover check: partition, Farkas certificates, and own enumeration of
realizable 4-point patterns (exact witnesses + exact Fourier-Motzkin infeasibility)."""
import json, sys, time, itertools, random
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog

import os
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..') + os.sep
cover = json.load(open(D + 'cover_n4.json'))
cuts = [F(c) for c in cover['cuts']]
forms = cover['form_order']
N = len(forms)


def form_vec_x(f):
    """coefficients in x1..x4 (0-indexed), form value f(x)."""
    v = [F(0)] * 4
    if f[0] == 'pair':
        i, j, c = f[1:]
        v[j] += 1
        v[i] -= cuts[c]
    else:
        a, b, c, d = f[1:]
        v[a] += 1; v[b] += 1; v[c] += 1; v[d] -= 2
    return v


def to_gaps(v):
    # x_k = g_0+...+g_k  ->  coefficient of g_m = sum_{k>=m} v_k
    return [sum(v[m:]) for m in range(4)]


FX = [form_vec_x(f) for f in forms]
FG = [to_gaps(v) for v in FX]


def sigma(ch, conv):
    # conv 'plus_neg': '+' means f<0. Pattern constraint: sigma*f < 0
    if conv == 'plus_neg':
        return 1 if ch == '+' else -1
    else:
        return -1 if ch == '+' else 1


def check_farkas(conv='plus_neg', pruned=None):
    pruned = cover['pruned'] if pruned is None else pruned
    bad = []
    for pref, ws in pruned.items():
        comb = [F(0)] * 4
        anypos = False
        for k, w in ws.items():
            k = int(k); w = F(w)
            if w < 0 or k >= len(pref):
                bad.append((pref, 'weight/index')); break
            if w > 0:
                anypos = True
            s = sigma(pref[k], conv)
            for m in range(4):
                comb[m] += w * s * FG[k][m]
        else:
            if not anypos or any(c < 0 for c in comb):
                bad.append((pref, [str(c) for c in comb]))
    return bad


def check_partition(patterns=None, pruned=None):
    patterns = cover['patterns'] if patterns is None else patterns
    pruned = cover['pruned'] if pruned is None else pruned
    pats = set(patterns)
    pr = set(pruned)
    problems = []
    if len(pats) != len(patterns):
        problems.append('duplicate patterns')
    if pats & pr:
        problems.append('pattern also pruned')
    keys = pats | pr
    # all prefixes of keys (proper)
    proper = set()
    for k in keys:
        for l in range(len(k)):
            proper.add(k[:l])
    for k in keys:
        if k in proper:
            problems.append(('key is proper prefix of another key', k))
    reached = set()
    # tree walk
    stack = ['']
    leaves = 0
    while stack:
        s = stack.pop()
        if s in keys:
            reached.add(s); leaves += 1
            continue
        if len(s) == N:
            problems.append(('uncovered full string', s)); continue
        if s not in proper and len(s) > 0:
            problems.append(('uncovered prefix', s)); continue
        stack.append(s + '+'); stack.append(s + '-')
    if reached != keys:
        problems.append(('unreached keys', len(keys - reached)))
    for p in patterns:
        if len(p) != N:
            problems.append(('pattern bad length', p))
    return problems


def brute_partition():
    """count, over all 2^20 strings, the number of keys that are prefixes."""
    pats = set(cover['patterns']); pr = set(cover['pruned'])
    keys = pats | pr
    lens = sorted({len(k) for k in keys})
    cnt = {0: 0, 1: 0, 2: 0}
    for bits in range(1 << N):
        s = ''.join('+' if (bits >> (N - 1 - i)) & 1 else '-' for i in range(N))
        c = sum(1 for l in lens if s[:l] in keys)
        cnt[min(c, 2)] += 1
    return cnt


# ---------- own realizability enumeration
def constraints(pref):
    # rows a with a.g < 0 required: sigma*FG + positivity -g_m<0
    rows = []
    for k, ch in enumerate(pref):
        s = 1 if ch == '+' else -1
        rows.append([s * c for c in FG[k]])
    for m in range(4):
        e = [F(0)] * 4; e[m] = F(-1); rows.append(e)
    return rows


def witness(rows):
    A = np.array([[float(c) for c in r] for r in rows])
    # maximize t s.t. A g + t <= 0, sum g = 1, t <= 1
    nvar = 5
    c = np.zeros(nvar); c[4] = -1
    A_ub = np.hstack([A, np.ones((len(rows), 1))])
    b_ub = np.zeros(len(rows))
    A_eq = np.array([[1, 1, 1, 1, 0]]); b_eq = [1]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=[(None, None)] * 4 + [(None, 1)], method='highs')
    if res.status != 0 or -res.fun < 1e-12:
        return None
    g = res.x[:4]
    for den in [10**3, 10**5, 10**7, 10**9, 10**12]:
        gq = [F(round(x * den), den) for x in g]
        if all(sum(a * b for a, b in zip(r, gq)) < 0 for r in rows):
            return gq
    return None


def normalize(r):
    m = max(abs(c) for c in r)
    if m == 0:
        return tuple(r)
    return tuple(c / m for c in r)


def fm_infeasible(rows):
    """Exact FM for strict homogeneous system a.g<0. Returns True iff infeasible."""
    S = {normalize(r) for r in rows}
    for v in range(3, -1, -1):
        if any(all(c == 0 for c in r) for r in S):
            return True
        pos = [r for r in S if r[v] > 0]
        negs = [r for r in S if r[v] < 0]
        zero = [r for r in S if r[v] == 0]
        new = set(zero)
        for p in pos:
            for n in negs:
                comb = tuple(p[i] * (-n[v]) + n[i] * p[v] for i in range(4))
                new.add(normalize(comb))
        S = new
        if not S:
            return False
    return any(all(c == 0 for c in r) for r in S)


def enumerate_realizable():
    real = []
    stats = dict(nodes=0, fm_calls=0, witness_fail_fm_feasible=0)
    stack = ['']
    while stack:
        s = stack.pop()
        stats['nodes'] += 1
        rows = constraints(s)
        w = witness(rows)
        if w is None:
            stats['fm_calls'] += 1
            if fm_infeasible(rows):
                continue
            stats['witness_fail_fm_feasible'] += 1
            raise RuntimeError('LP missed a feasible node ' + s)
        if len(s) == N:
            real.append((s, w))
            continue
        stack.append(s + '+'); stack.append(s + '-')
    return real, stats


def pattern_of_point(x):
    s = ''
    for k in range(N):
        val = sum(a * b for a, b in zip(FX[k], x))
        assert val != 0
        s += '+' if val < 0 else '-'
    return s


if __name__ == '__main__':
    t = time.time()
    print('patterns', len(cover['patterns']), 'pruned', len(cover['pruned']))
    b1 = check_farkas('plus_neg')
    print('Farkas failures (convention + means f<0):', len(b1))
    b2 = check_farkas('plus_pos')
    print('Farkas failures (control, opposite convention):', len(b2))
    pp = check_partition()
    print('partition problems:', pp[:5], len(pp))
    print('brute 2^20 coverage counts {0 keys,1 key,>=2 keys}:', brute_partition())
    real, stats = enumerate_realizable()
    print('realizable patterns found:', len(real), stats)
    pats = set(cover['patterns'])
    realset = {s for s, _ in real}
    for s, w in real:
        x = [sum(w[:k + 1]) for k in range(4)]
        assert pattern_of_point(x) == s
    print('realizable not retained:', sorted(realset - pats))
    print('retained not realizable:', len(pats - realset), sorted(pats - realset)[:10])
    # pruned prefixes must contain no realizable pattern
    hit = [p for p in cover['pruned'] if any(s.startswith(p) for s in realset)]
    print('pruned prefixes containing a realizable pattern:', len(hit))
    json.dump({s: [str(c) for c in w] for s, w in real},
              open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'realizable_n4.json'), 'w'), indent=0)
    print('time', time.time() - t)
