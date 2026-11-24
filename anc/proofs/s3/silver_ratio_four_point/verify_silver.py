"""S3(1+sqrt2) < 1/2 with a four-point colored certificate. Standard library only.
Checks: exact partition of the sign space by retained patterns and excluded prefixes; every
Gordan exclusion over Q(sqrt2); positive definiteness of every block; every pattern score
<= BOUND; BOUND < 1/2. Run: python3 verify_silver.py"""
import sys, os
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cover import load_cover, build_forms, partition_check, farkas_check
from cert import load_cert, psd_enclosure, ldl_exact, gram, check_scores
HERE = os.path.dirname(os.path.abspath(__file__))
BOUND = F("498858810079997743907193/1000000000000000000000000")
cov, K, c, cuts, parse = load_cover(os.path.join(HERE, "silver_n4_cover.json"))
forms = build_forms(K, c, cuts)
part = partition_check(cov["patterns"], cov["pruned"].keys(), len(forms))
assert part["partition_ok"], part
bad = [p for p, w in cov["pruned"].items() if not farkas_check(K, forms, p, w, parse)[0]]
assert not bad, bad[:3]
d, V, blocks = load_cert(os.path.join(HERE, "silver_n4_certificate.json"))
assert d["c"] == cov["c"] and d["cuts"] == cov["cuts"]
for b in blocks:
    ok, _, _ = psd_enclosure(V, b["Y"]); signs, ok2 = ldl_exact(V, b["Y"])
    assert ok and ok2 and all(s > 0 for s in signs)
Qs = [gram(V, b["W"], b["Y"]) for b in blocks]
res = check_scores(V, cov["patterns"], blocks, Qs, len(cuts), V.elem([BOUND]))
assert not res["violations"] and res["n"] == len(cov["patterns"])
assert BOUND < F(1, 2)
print("patterns", res["n"], "exclusions", len(cov["pruned"]), "tight", len(res["tight"]))
print("S3(1+sqrt2) <=", BOUND, "=", float(BOUND), "< 1/2: verified")
