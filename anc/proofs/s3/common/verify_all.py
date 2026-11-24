"""Recheck all saved upper certificates and lower witnesses, without a solver."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from anc.proofs.paths import data_path
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path

from verify import verify

HERE = Path(__file__).resolve().parent


def verify_lower(case):
    c = Q(case["c"])
    support = list(map(Q, case["support_exact"]))
    masses = list(map(Q, case["masses_exact"]))
    rho = Q(case["safe_scale_ratio_exact"])
    assert 0 < c < 3
    assert support == sorted(set(support)) and support[0] == 0 and support[-1] == 1
    assert len(support) == len(masses)
    assert min(masses) >= 0 and sum(masses) == 1 and masses[0] < 1
    probability, minimum_slack = Q(0), None
    for indices in product(range(len(support)), repeat=4):
        slack = c * support[indices[3]] - sum(support[i] for i in indices[:3])
        if slack > 0:
            weight = Q(1)
            for i in indices:
                weight *= masses[i]
            probability += weight
            minimum_slack = slack if minimum_slack is None else min(slack, minimum_slack)
    # Replacing zero draws by values <=rho preserves every base success.
    # The all-zero event repeats the construction, with probability p0**4.
    assert minimum_slack is not None and 0 < rho < support[1]
    assert 3 * rho < minimum_slack and c * rho < support[1]
    bound = probability / (1 - masses[0] ** 4)
    assert bound == Q(case["recursive_probability_exact"])
    return bound


def verify_uniform_above_silver(case):
    """Check the fixed masses against the paper's uniform window polynomial."""
    bound = verify_lower(case)
    c = Q(case["c"])
    support = list(map(Q, case["support_exact"]))
    assert len(support) == 3 and 1 / (c - 1) < support[1] < (c - 1) / 2
    z, a, b = map(Q, case["masses_exact"])
    numerator = (
        a * (z ** 3 + 3 * z ** 2 * (a + b) + 3 * z * (a ** 2 + 2 * a * b))
        + b * (z ** 3 + 3 * z ** 2 * (a + b) + 3 * z * (a + b) ** 2 + a ** 3)
        + 3 * a ** 2 * b ** 2
    )
    # This polynomial counts successes throughout the nonempty window,
    # which exists for every 1+sqrt(2)<c<3. Larger c follow by monotonicity.
    assert numerator / (1 - z ** 4) == bound
    return bound


def verify_uniform_after_first(case):
    """Check fixed masses for the window opening at (1+sqrt(13))/2."""
    bound = verify_lower(case)
    c = Q(case["c"])
    support = list(map(Q, case["support_exact"]))
    assert len(support) == 3 and 1 / (c - 1) < support[1] < c / 3
    z, a, b = map(Q, case["masses_exact"])
    numerator = (
        a * (z ** 3 + 3 * z ** 2 * (a + b) + 3 * z * (a ** 2 + 2 * a * b))
        + b * (z ** 3 + 3 * z ** 2 * (a + b) + 3 * z * (a + b) ** 2 + a ** 3)
    )
    assert numerator / (1 - z ** 4) == bound
    return bound


def verify_uniform_after_sqrt2(case):
    """Fixed masses for 1/c<r<c/2, a nonempty window whenever c>sqrt(2)."""
    bound = verify_lower(case)
    c = Q(case["c"])
    support = list(map(Q, case["support_exact"]))
    assert len(support) == 3 and 1 / c < support[1] < c / 2
    z, a, b = map(Q, case["masses_exact"])
    numerator = (a + b) * z ** 3 + 3 * (a + b) ** 2 * z ** 2 + 3 * z * a ** 2 * b
    assert numerator / (1 - z ** 4) == bound
    return bound


def main():
    for certificate_path in sorted((HERE.parent / "rational").glob("n[456]_c*_certificate.json")):
        cover_path = data_path(
            certificate_path.name.replace("_certificate.json", "_cover.json"),
            family="s3")
        result = verify(json.loads(cover_path.read_text()), json.loads(certificate_path.read_text()))
        report_path = data_path(
            certificate_path.name.replace("_certificate.json", "_report.json"),
            family="s3")
        saved = json.loads(report_path.read_text())
        assert all(saved[key] == value for key, value in result.items())
        print(f"{certificate_path.name}: upper {result['upper_decimal']:.12f}, exact checks passed")
    from verify_below_two import verify as verify_below_two
    below_result = verify_below_two(
        json.loads((data_path("below_two_sqrt2_cover.json", family="s3")).read_text()),
        json.loads((data_path("below_two_sqrt2_field_certificate.json", family="s3")).read_text()),
    )
    assert below_result == json.loads((data_path("below_two_sqrt2_verification.json", family="s3")).read_text())
    print(f"exact plateau below two: {below_result['bound_decimal']:.12f}, "
          f"{below_result['tight_patterns']} tight patterns, exact checks passed")
    from below_two_field import Value as BelowValue, B as BelowB
    uniform_below = json.loads((data_path("below_two_uniform_jump.json", family="s3")).read_text())
    below_lower = verify_uniform_after_sqrt2(uniform_below)
    assert BelowValue(below_lower) - BelowB > Q("0.011685187")
    print(f"uniform after sqrt(2): lower {float(below_lower):.12f}; "
          "jump >0.011685187, exact checks passed")
    for filename in ("below_two_lower.json", "below_two_insertion.json"):
        for row in json.loads((data_path(filename, family="s3")).read_text())["cases"]:
            for case in row["ladders"]:
                verify_lower(case)
            bound = verify_lower(row["best"])
            print(f"{filename}, c={row['c']}: lower {float(bound):.12f}, exact checks passed")
    baseline = json.loads((data_path("lower_baseline.json", family="s3")).read_text())
    bound = verify_lower(baseline)
    assert list(map(Q, baseline["support_exact"])) == [Q(0), Q(1)]
    w = Q(baseline["masses_exact"][1])
    assert bound == (w - w ** 4) / (1 - (1 - w) ** 4)
    print(f"single-atom family: lower {float(bound):.12f}, exact checks passed")
    for case in json.loads((data_path("lower_ladders.json", family="s3")).read_text())["cases"]:
        bound = verify_lower(case)
        print(f"c={case['c']}: lower {float(bound):.12f}, exact checks passed")
    for filename in ("lower_scout.json", "lower_thresholds.json"):
        for case in json.loads((data_path(filename, family="s3")).read_text())["cases"]:
            bound = verify_lower(case)
            if "threshold_bracket" in case:
                lo, hi = map(Q, case["threshold_bracket"])
                assert hi == Q(case["c"]) and hi - lo <= Q(1, 10 ** 9)
                for coefficient, expected in ((lo, False), (hi, True)):
                    atom = Q(1)
                    for _ in range(case["tail_atoms"]):
                        atom = (2 + atom) / coefficient
                    assert (atom < coefficient - 1) == expected
            print(f"{filename}, c={case['c']}: lower {float(bound):.12f}, exact checks passed")
    uniform = json.loads((data_path("lower_uniform.json", family="s3")).read_text())
    print(f"uniform above silver: lower {float(verify_uniform_above_silver(uniform)):.12f}, exact checks passed")
    from verify_endpoint import verify as verify_endpoint
    endpoint_result = verify_endpoint(
        json.loads((data_path("endpoint_n4_cover.json", family="s3")).read_text()),
        json.loads((data_path("endpoint_n4_field_certificate.json", family="s3")).read_text()),
    )
    saved_endpoint = json.loads((data_path("endpoint_n4_verification.json", family="s3")).read_text())
    assert saved_endpoint == endpoint_result
    print(f"exact first plateau: {endpoint_result['bound_decimal']:.12f}, "
          f"{endpoint_result['tight_patterns']} tight patterns, exact checks passed")
    from verify_second_plateau import verify as verify_second_plateau
    second_result = verify_second_plateau(
        json.loads((data_path("n4_c47-20_cuts47-40_60-47_27-20_47-27_47-20_cover.json", family="s3")).read_text()),
        json.loads((data_path("second_plateau_n4_field_certificate.json", family="s3")).read_text()),
    )
    assert second_result == json.loads((data_path("second_plateau_n4_verification.json", family="s3")).read_text())
    print(f"exact interval after first jump: {second_result['bound_decimal']:.12f}, "
          f"{second_result['tight_patterns']} tight patterns, exact checks passed")
    from endpoint_field import Value, B
    first = json.loads((data_path("lower_thresholds.json", family="s3")).read_text())["cases"][0]
    right_lower = verify_uniform_after_first(first)
    jump = Value(right_lower) - B
    assert jump > Q("0.008374335")
    print(f"uniform after first endpoint: {float(right_lower):.12f}; "
          "jump >0.008374335, exact checks passed")


if __name__ == "__main__":
    main()
