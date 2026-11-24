"""Exact arithmetic for the candidate two-positive-atom S3 plateau value.

The isolated generator is t=2/(3z-1)-14. Its defining polynomial has
a unique root in (1,2), certified by the shared field's derivative test.
Stationarity is useful for search, but does not assert global optimality.
"""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from algebraic_field import make_field
sys.path.pop(0)

POLYNOMIAL = [
    -66740403979049453502464, -18402112159442665381888,
    18061971300259211173888, 13902317223893986129408,
    4662461182870440581120, 971351107961113199488,
    139789017733010751168, 14561509316469512736,
    1120982904192756048, 64058791131697672, 2690862168469796,
    80897380082608, 1650220285480, 20489041874, 117010873,
]
ROOT_INTERVAL = (1, 2)
Value = make_field(POLYNOMIAL, root_interval=ROOT_INTERVAL, local_isolation=True)
T = Value([0, 1] + [0] * 12)
Z = (T + 16) / (3 * T + 42)


def evaluate(coefficients, x):
    result = x - x
    for coefficient in reversed(coefficients):
        result = result * x + coefficient
    return result


def masses_and_value(z):
    denominator = evaluate([36, -72, -168, -115, 46, -102, -154, -123, 4], z)
    numerator = evaluate([12, 96, -204, -121, -92, 205, -184, -172, -94, 68], z)
    a = -numerator / denominator
    b = 1 - z - a
    n = (1 - z) - (1 - z) ** 4 + a * b * (a ** 2 - 3 * z * b)
    return a, b, n / (1 - z ** 4)


A, D, B = masses_and_value(Z)
assert 0 < Z < 1 and A > 0 and D > 0 and Z + A + D == 1
assert (-4 * A ** 3 - 12 * A ** 2 * Z + 3 * A ** 2
        - 12 * A * Z ** 2 + 12 * A * Z - 3 * Z ** 3 + 6 * Z ** 2 - 3 * Z) == 0
_numerator = (1 - Z) - (1 - Z) ** 4 + A * D * (A ** 2 - 3 * Z * D)
_z_derivative = -1 + 4 * (1 - Z) ** 3 - A ** 3 - 3 * A * D ** 2 + 6 * A * Z * D
assert (1 - Z ** 4) * _z_derivative + 4 * Z ** 3 * _numerator == 0


@lru_cache(None)
def root_interval(bits):
    lo, hi = Q(1), Q(2)
    for _ in range(bits):
        mid = (lo + hi) / 2
        if evaluate(POLYNOMIAL, mid) < 0:
            lo = mid
        else:
            hi = mid
    return lo, hi


def reliable_float(value):
    """Avoid catastrophic cancellation in degree-14 power coordinates."""
    for bits in (128, 256, 512, 1024, 2048):
        lo, hi = root_interval(bits)
        lower = upper = value.v[-1]
        for coefficient in reversed(value.v[:-1]):
            products = (lower * lo, lower * hi, upper * lo, upper * hi)
            lower, upper = min(products) + coefficient, max(products) + coefficient
        if float(lower) == float(upper):
            return float(lower)
    raise ArithmeticError("Unresolved floating approximation of degree-14 value")


Value.__float__ = reliable_float


def enclosure(value, bits):
    lo, hi = root_interval(bits)
    lower = upper = value.v[-1]
    for coefficient in reversed(value.v[:-1]):
        products = (lower * lo, lower * hi, upper * lo, upper * hi)
        lower, upper = min(products) + coefficient, max(products) + coefficient
    return lower, upper


def positive_definite(matrix):
    """Rigorous rational comparison, avoiding large field LDL coefficients.

    If every entry differs from R by at most epsilon, then
    Y >= R-n*epsilon*I in the order on symmetric matrices. Exact rational
    LDL on that smaller matrix proves Y positive definite.
    """
    a = [[Value(x) for x in row] for row in matrix]
    n = len(a)
    assert n and all(len(row) == n for row in a)
    assert all(a[i][j] == a[j][i] for i in range(n) for j in range(n))
    denominator = 10 ** 10
    for bits in (128, 256, 512, 1024, 2048, 4096):
        rounded = [[Q(0) for _ in range(n)] for _ in range(n)]
        error = Q(0)
        for i in range(n):
            for j in range(i, n):
                lo, hi = enclosure(a[i][j], bits)
                midpoint = (lo + hi) / 2
                scaled = midpoint * denominator + Q(1, 2)
                value = Q(scaled.numerator // scaled.denominator, denominator)
                rounded[i][j] = rounded[j][i] = value
                error = max(error, abs(lo - value), abs(hi - value))
        if error < Q(1, 10 ** 8):
            break
    else:
        raise ArithmeticError("Algebraic matrix enclosure did not converge")
    scaled = error * denominator
    epsilon = Q(-(-scaled.numerator // scaled.denominator), denominator)
    a = rounded
    for i in range(n):
        a[i][i] -= n * epsilon
    for k in range(n):
        assert a[k][k] > 0, ("nonpositive exact LDL pivot", k, float(a[k][k]))
        for i in range(k + 1, n):
            factor = a[i][k] / a[k][k]
            for j in range(i, n):
                a[j][i] = a[i][j] = a[i][j] - factor * a[k][j]
    return True


if __name__ == "__main__":
    print({"zero_mass": float(Z), "small_atom_mass": float(A),
           "large_atom_mass": float(D), "candidate_value": float(B)})
