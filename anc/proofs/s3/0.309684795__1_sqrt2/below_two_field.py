"""Exact candidate value for the one-atom-per-scale construction below 2."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from algebraic_field import make_field
sys.path.pop(0)

POLYNOMIAL = [-5, -4, -3, 6]
ROOT_INTERVAL = (1, 2)
Value = make_field(POLYNOMIAL, root_interval=ROOT_INTERVAL, local_isolation=True)
U = Value([0, 1, 0])
Z = 1 / U
B = Z ** 2 * (3 - 2 * Z) / (1 + Z + Z ** 2 + Z ** 3)
assert 0 < Z < 1 and 5 * Z ** 3 + 4 * Z ** 2 + 3 * Z - 6 == 0


def positive_definite(matrix):
    a = [[Value(x) for x in row] for row in matrix]
    n = len(a)
    assert n and all(len(row) == n for row in a)
    assert all(a[i][j] == a[j][i] for i in range(n) for j in range(n))
    for k in range(n):
        assert a[k][k] > 0, ("nonpositive exact LDL pivot", k, float(a[k][k]))
        for i in range(k + 1, n):
            factor = a[i][k] / a[k][k]
            for j in range(i, n):
                a[j][i] = a[i][j] = a[i][j] - factor * a[k][j]
    return True
