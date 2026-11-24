"""Standard-library arithmetic for the first S3 plateau value."""

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

# u=1/z is the unique root in (2,3); p'(2+y) has positive coefficients.
Value = make_field([4, -4, -3, -6, 3], root_interval=(2, 3), local_isolation=True)
U = Value([0, 1, 0, 0])
Z = 1 / U
B = (3 * Z - 3 * Z ** 2 + Z ** 3) / (1 + Z + Z ** 2 + Z ** 3)
assert 0 < Z < 1 and 4 * Z ** 4 - 4 * Z ** 3 - 3 * Z ** 2 - 6 * Z + 3 == 0


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
