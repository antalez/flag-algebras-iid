"""Check completeness failures and the target rank newly possible above two."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from anc.proofs.paths import data_path
import copy
from fractions import Fraction as Q
from itertools import permutations
import json
from pathlib import Path
import unittest

from verify import forms, verify, verify_cover
from verify_all import verify_lower, verify_uniform_above_silver

HERE = Path(__file__).resolve().parent
STEM = "n4_c23-10_cuts23-20_13-10_23-13_23-10"


class VerificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cover = json.loads((data_path(STEM + "_cover.json", family="s3")).read_text())
        cls.cert = json.loads((data_path(STEM + "_certificate.json", family="s3")).read_text())

    def test_second_smallest_can_win(self):
        points = [Q(1, 100), Q(1), Q(101, 100), Q(102, 100)]
        c = Q(23, 10)
        wins = [sum(points) - point < c * point for point in points]
        self.assertEqual(wins, [False, True, True, True])
        probability = Q(sum(sum(x[:3]) < c * x[3] for x in permutations(points)), 24)
        self.assertEqual(probability, Q(3, 4))
        targets = [target for kind, _, target in forms(4, []) if kind == "sum"]
        self.assertEqual(Q(sum(wins[target] for target in targets), 4), probability)

    def test_missing_pattern_rejected(self):
        cover = copy.deepcopy(self.cover)
        cover["patterns"].pop()
        with self.assertRaisesRegex(AssertionError, "Gap or overlap"):
            verify_cover(cover)

    def test_negative_exclusion_weight_rejected(self):
        cover = copy.deepcopy(self.cover)
        proof = next(iter(cover["pruned"].values()))
        proof[next(iter(proof))] = "-1"
        with self.assertRaises(AssertionError):
            verify_cover(cover)

    def test_false_claimed_bound_rejected(self):
        cert = copy.deepcopy(self.cert)
        cert["bound"] = "0"
        with self.assertRaises(AssertionError):
            verify(self.cover, cert)

    def test_unweighted_patterns_have_three_quarters_bound(self):
        cert = dict(n=4, c=self.cover["c"], cuts=self.cover["cuts"], blocks=[])
        self.assertEqual(Q(verify(self.cover, cert)["bound"]), Q(3, 4))

    def test_lower_witness_and_false_claim(self):
        case = json.loads((data_path("lower_ladders.json", family="s3")).read_text())["cases"][0]
        self.assertGreater(verify_lower(case), Q(4911, 10000))
        case["recursive_probability_exact"] = "1"
        with self.assertRaises(AssertionError):
            verify_lower(case)

    def test_uniform_window_mass_improvement(self):
        case = json.loads((data_path("lower_uniform.json", family="s3")).read_text())
        self.assertGreater(verify_uniform_above_silver(case), Q(503419372, 10 ** 9))
        self.assertGreater(verify_uniform_above_silver(case), Q(7808829037, 15517440000))


if __name__ == "__main__":
    unittest.main()
