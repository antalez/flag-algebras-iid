"""Independent certificate checks: PSD of Y (exact LDL in the field and a
rational-enclosure argument), M_sigma(P) from the definitions, exact scores."""
import json, itertools, time
from fractions import Fraction as F
from math import comb
from nf import NumberField, sgn

PAIRS4 = list(itertools.combinations(range(4), 2))


def load_cert(path, K=None):
    d = json.load(open(path))
    V = NumberField(d["value_polynomial"], d["value_root_interval"], "u")
    blocks = []
    for b in d["blocks"]:
        W = [[V.elem(e) for e in row] for row in b["basis"]]
        Y = [[V.elem(e) for e in row] for row in b["matrix"]]
        blocks.append(dict(t=b["t"], f=b["f"], type=b["type"], flags=list(b["flags"]), W=W, Y=Y))
    return d, V, blocks


# ---------------------------------------------------------------- restriction / flags
def sub_code(P, S, m, bit_order="pair_major"):
    """code of the sub-configuration on sorted vertex tuple S (pair forms only)."""
    code = 0
    loc = list(itertools.combinations(range(len(S)), 2))
    for li, (a, b) in enumerate(loc):
        gi = PAIRS4.index((S[a], S[b]))
        for q in range(m):
            if P[gi * m + q] == "+":
                bit = li * m + q if bit_order == "pair_major" else q * len(loc) + li
                code += 1 << bit
    return code


def flag_code(P, R, A, f, t, m, bit_order="pair_major"):
    S = tuple(sorted(R + A))
    marks = list(itertools.combinations(range(f), t))
    pos = tuple(sorted(S.index(r) for r in R))
    return sub_code(P, S, m, bit_order) * len(marks) + marks.index(pos)


def M_matrix(P, blk, m, bit_order="pair_major"):
    """dict {(i,j): Fraction} over positions in blk['flags']."""
    t, f = blk["t"], blk["f"]
    pos = {}
    for i, fl in enumerate(blk["flags"]):
        pos.setdefault(fl, []).append(i)
    denom = comb(4, t) * comb(4 - t, f - t) * comb(4 - f, f - t)
    M = {}
    cnt = 0
    for R in itertools.combinations(range(4), t):
        if sub_code(P, R, m, bit_order) != blk["type"]:
            # count triples anyway for the denominator sanity check
            rest = [v for v in range(4) if v not in R]
            for A in itertools.combinations(rest, f - t):
                rest2 = [v for v in rest if v not in A]
                for B in itertools.combinations(rest2, f - t):
                    cnt += 1
            continue
        rest = [v for v in range(4) if v not in R]
        for A in itertools.combinations(rest, f - t):
            rest2 = [v for v in rest if v not in A]
            fa = flag_code(P, R, A, f, t, m, bit_order)
            for B in itertools.combinations(rest2, f - t):
                cnt += 1
                fb = flag_code(P, R, B, f, t, m, bit_order)
                for i in pos.get(fa, []):
                    for j in pos.get(fb, []):
                        M[(i, j)] = M.get((i, j), F(0)) + F(1, denom)
    assert cnt == denom, (cnt, denom)
    return M


def obj(P):
    return F(P[-3:].count("+"), 4)


# ---------------------------------------------------------------- Q = W Y W^T
def gram(V, W, Y):
    nW, k = len(W), len(Y)
    WY = [[None] * k for _ in range(nW)]
    for i in range(nW):
        for j in range(k):
            s = V.zero()
            for l in range(k):
                if any(W[i][l]) and any(Y[l][j]):
                    s = V.add(s, V.mul(W[i][l], Y[l][j]))
            WY[i][j] = s
    Q = [[None] * nW for _ in range(nW)]
    for i in range(nW):
        for j in range(nW):
            s = V.zero()
            for l in range(k):
                if any(WY[i][l]) and any(W[j][l]):
                    s = V.add(s, V.mul(WY[i][l], W[j][l]))
            Q[i][j] = s
    return Q


# ---------------------------------------------------------------- PSD
def symmetric(V, Y):
    k = len(Y)
    return all(Y[i][j] == Y[j][i] for i in range(k) for j in range(k))


def ldl_exact(V, Y):
    """exact LDL^T in the field; returns list of pivot signs (None if a zero
    pivot appears before the end)."""
    k = len(Y)
    A = [[list(x) for x in row] for row in Y]
    signs = []
    for p in range(k):
        s = V.sign(A[p][p])
        signs.append(s)
        if s <= 0:
            return signs, False
        inv = V.inv(A[p][p])
        for i in range(p + 1, k):
            if not any(A[i][p]):
                continue
            l = V.mul(A[i][p], inv)
            for j in range(p + 1, k):
                if any(A[p][j]):
                    A[i][j] = V.sub(A[i][j], V.mul(l, A[p][j]))
    return signs, True


def psd_enclosure(V, Y, bits=300):
    """Rigorous: Y = Y0 + E, |E_ij| <= delta (rational enclosure of each
    entry); exact rational LDL of Y0 - eps I with eps = k*delta >= ||E||_2.
    If all pivots > 0 then Y is positive definite."""
    V.refine(bits)
    k = len(Y)
    Y0 = [[None] * k for _ in range(k)]
    delta = F(0)
    for i in range(k):
        for j in range(k):
            val, err = V.approx(Y[i][j])
            Y0[i][j] = val
            delta = max(delta, err)
    # make Y0 exactly symmetric (Y symmetric => same enclosure anyway)
    for i in range(k):
        for j in range(i):
            assert Y0[i][j] == Y0[j][i]
    eps = k * delta
    A = [[Y0[i][j] - (eps if i == j else 0) for j in range(k)] for i in range(k)]
    piv = []
    for p in range(k):
        d = A[p][p]
        piv.append(d)
        if d <= 0:
            return False, float(delta), [float(x) for x in piv]
        for i in range(p + 1, k):
            if A[i][p] == 0:
                continue
            l = A[i][p] / d
            for j in range(p + 1, k):
                if A[p][j]:
                    A[i][j] -= l * A[p][j]
    return True, float(delta), [float(x) for x in piv]


# ---------------------------------------------------------------- scores
def score(V, P, blocks, Qs, m, bit_order="pair_major"):
    s = V.elem([obj(P)])
    for blk, Q in zip(blocks, Qs):
        M = M_matrix(P, blk, m, bit_order)
        for (i, j), w in M.items():
            if any(Q[i][j]):
                s = V.add(s, V.scale(Q[i][j], w))
    return s


def check_scores(V, patterns, blocks, Qs, m, bound, bit_order="pair_major", stop_on_fail=False):
    res = {"n": 0, "violations": [], "tight": [], "max_float": None, "min_slack_nontight": None}
    mx = None
    minsl = None
    for P in patterns:
        s = score(V, P, blocks, Qs, m, bit_order)
        diff = V.sub(bound, s)
        sg = V.sign(diff)
        res["n"] += 1
        fs = V.to_float(s)
        if mx is None or fs > mx[0]:
            mx = (fs, P)
        if sg < 0:
            res["violations"].append((P, V.to_float(diff)))
            if stop_on_fail:
                break
        elif sg == 0:
            res["tight"].append(P)
        else:
            sl = V.to_float(diff)
            if minsl is None or sl < minsl[0]:
                minsl = (sl, P)
    res["max_float"] = mx
    res["min_slack_nontight"] = minsl
    return res
