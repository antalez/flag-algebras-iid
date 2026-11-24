"""Try to certify that the implemented six-point SDP cannot reach 1/2.

A feasible pattern pseudodistribution is not an iid counterexample. Exact
positive definite moment matrices certify only an obstruction to this SDP.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from flag_sdp import assemble, np, sparse, unpack
import clarabel
from sharp_certificate_obstruction import positive_definite_bareiss


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cover", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--seconds", type=float, default=90)
    p.add_argument("--support", type=Path, help="Use indices from a saved numerical primal")
    p.add_argument("--check-saved", type=Path, help="Check saved indices/weights without solving")
    args = p.parse_args()
    data = json.loads(args.cover.read_text())
    patterns, objective, blocks = assemble(data)
    support = args.check_saved or args.support
    indices = np.arange(len(patterns)) if support is None else np.load(support)["indices"]
    patterns, objective = patterns[indices], objective[indices]
    blocks = [dict(b, operator=b["operator"][:, indices], counts=b["counts"][:, indices]) for b in blocks]
    n = len(patterns)
    # Maximize a common strictly positive eigenvalue margin while retaining
    # an objective above 1/2. The last variable is this margin.
    rows = [sparse.csc_matrix(np.r_[np.ones(n), 0][None, :]),
            sparse.hstack([-sparse.eye(n), sparse.csc_matrix((n, 1))]),
            sparse.csc_matrix(np.r_[-objective, 0][None, :])]
    for b in blocks:
        identity = np.array([int(i == j) for i, j in b["pairs"]])[:, None]
        rows.append(sparse.hstack([-b["operator"], sparse.csc_matrix(identity)]))
    a = sparse.vstack(rows, format="csc")
    rhs = np.zeros(a.shape[0]); rhs[0] = 1; rhs[n+1] = -.5005
    cones = [clarabel.ZeroConeT(1), clarabel.NonnegativeConeT(n+1)]
    cones += [clarabel.PSDTriangleConeT(len(b["flags"])) for b in blocks]
    c = np.zeros(n+1); c[-1] = -1
    settings = clarabel.DefaultSettings()
    settings.verbose = False; settings.max_threads = 2
    settings.time_limit = args.seconds; settings.max_iter = 150
    settings.tol_feas = settings.tol_gap_abs = settings.tol_gap_rel = 1e-10
    if args.check_saved:
        weights = np.load(args.check_saved)["weights"]
        report = dict(status="Checking saved weights", objective=float(objective@weights))
    else:
        result = clarabel.DefaultSolver(sparse.csc_matrix((n+1, n+1)), c, a, rhs, cones, settings).solve()
        weights = np.array(result.x[:-1])
        report = dict(status=str(result.status), objective=float(objective@weights),
                      margin=float(result.x[-1]), seconds=result.solve_time)
    print(json.dumps(report), flush=True)
    np.savez_compressed(args.output.with_suffix(".npz"), indices=indices, weights=weights)
    denominator = 10**12
    integers = [max(0, int(round(v*denominator))) for v in weights]
    denominator = sum(integers)
    value = sum(int(np.count_nonzero(p == 1))*w for p, w in zip(patterns, integers))
    value = Fraction(value, 60*denominator)
    if value <= Fraction(1, 2):
        raise ValueError("No rational objective above one half")
    checks, verified, failure = [], True, None
    for b in blocks:
        if b["norm"]*denominator >= 2**63:
            raise ValueError("Exact moment accumulation would overflow int64")
        packed = b["counts"] @ np.array(integers, dtype=np.int64)
        matrix = [[0]*len(b["flags"]) for _ in b["flags"]]
        for (i, j), v in zip(b["pairs"], packed):
            matrix[i][j] = matrix[j][i] = int(v)
        try:
            digits = positive_definite_bareiss(matrix)
        except ValueError as exc:
            verified, failure = False, str(exc)
            print(f"No certificate: block dimension {len(matrix)}: {exc}", flush=True)
            break
        checks.append(dict(t=b["t"], f=b["f"], type=b["type"], dimension=len(matrix),
                           positive_definite=True, largest_minor_digits=digits))
        print(f"Exact positive definiteness verified: {len(matrix)}x{len(matrix)}", flush=True)
    report.update(verified=verified, failure=failure,
                  exact_objective=str(value), exact_objective_decimal=float(value), blocks=checks,
                  indices=indices.tolist(),
                  weight_numerators=integers, weight_denominator=denominator,
                  interpretation="Pseudodistribution, NOT an iid distribution; obstruction only to the implemented SDP over this cover.")
    args.output.write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
