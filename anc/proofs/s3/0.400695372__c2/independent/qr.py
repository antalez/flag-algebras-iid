"""Independent Q(r) arithmetic. r root in (0,1) of p(x)=x^4-4x^3-3x^2-2x+2.
Elements: tuple (a0,a1,a2,a3) of Fractions meaning a0+a1 r+a2 r^2+a3 r^3.
Sign decision: exact zero test (p irreducible => zero iff all coeffs zero),
else interval evaluation on a rational enclosure [lo,hi] of r, refined by bisection."""
from fractions import Fraction as F

P = [F(2), F(-2), F(-3), F(-4), F(1)]  # coeffs low->high


def peval(x):
    return sum(c * x**i for i, c in enumerate(P))


# rational enclosure of r by bisection on (0,1) (p(0)=2>0, p(1)=-6<0)
_LO, _HI = F(0), F(1)
assert peval(_LO) > 0 and peval(_HI) < 0


def _refine(bits):
    global _LO, _HI
    while _HI - _LO > F(1, 2**bits):
        m = (_LO + _HI) / 2
        v = peval(m)
        if v == 0:
            raise RuntimeError("rational root")
        if v > 0:
            _LO = m
        else:
            _HI = m


_refine(80)

# r^4 = 4r^3+3r^2+2r-2
RED = (F(-2), F(2), F(3), F(4))


def make(a):
    return tuple(F(x) for x in a)


ZERO = make([0, 0, 0, 0])
ONE = make([1, 0, 0, 0])
R = make([0, 1, 0, 0])


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def scal(c, a):
    c = F(c)
    return tuple(c * x for x in a)


def mul(a, b):
    prod = [F(0)] * 7
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            if y:
                prod[i + j] += x * y
    for d in range(6, 3, -1):
        c = prod[d]
        if c:
            prod[d] = F(0)
            for k in range(4):
                prod[d - 4 + k] += c * RED[k]
    return tuple(prod[:4])


def interval(a, lo, hi):
    # r in [lo,hi] subset (0,1): powers monotone increasing, nonnegative
    L = H = F(0)
    for k, c in enumerate(a):
        pl, ph = lo**k, hi**k
        if c >= 0:
            L += c * pl
            H += c * ph
        else:
            L += c * ph
            H += c * pl
    return L, H


def sign(a):
    if all(x == 0 for x in a):
        return 0
    bits = 80
    while True:
        L, H = interval(a, _LO, _HI)
        if L > 0:
            return 1
        if H < 0:
            return -1
        bits *= 2
        if bits > 5000:
            raise RuntimeError("sign undecided")
        _refine(bits)


def inv(a):
    # solve a*x = 1 by linear algebra over Q (4x4)
    cols = []
    for k in range(4):
        e = [0, 0, 0, 0]
        e[k] = 1
        cols.append(mul(a, make(e)))
    # matrix M with M[:,k] = cols[k]; solve M x = (1,0,0,0)
    M = [[cols[k][i] for k in range(4)] + [F(1 if i == 0 else 0)] for i in range(4)]
    for c in range(4):
        piv = next(i for i in range(c, 4) if M[i][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for i in range(4):
            if i != c and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[c])]
    x = tuple(M[i][4] for i in range(4))
    assert mul(a, x) == ONE
    return x


def fval(a):
    m = (_LO + _HI) / 2
    return float(sum(c * m**k for k, c in enumerate(a)))


def rnum():
    return (_LO + _HI) / 2
