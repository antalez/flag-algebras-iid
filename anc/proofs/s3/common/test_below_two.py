"""Check the new exact plateau and rejection of incomplete or invalid proofs."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from anc.proofs.paths import data_path
import copy
from fractions import Fraction as Q
import json
from pathlib import Path
import unittest

from below_two_field import Value, Z, B
from verify_below_two import verify
from verify_all import verify_uniform_after_sqrt2

HERE = Path(__file__).resolve().parent


class BelowTwoTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cover = json.loads((data_path("below_two_sqrt2_cover.json", family="s3")).read_text())
        cls.certificate = json.loads((data_path("below_two_sqrt2_field_certificate.json", family="s3")).read_text())

    def test_exact_plateau_and_uniform_jump(self):
        result = verify(self.cover, self.certificate)
        self.assertEqual(result, json.loads((data_path("below_two_sqrt2_verification.json", family="s3")).read_text()))
        self.assertEqual(result["tight_patterns"], 9)
        self.assertAlmostEqual(float(B), .3096847954174251, places=14)
        self.assertEqual(5 * Z ** 3 + 4 * Z ** 2 + 3 * Z - 6, Value(0))
        case = json.loads((data_path("below_two_uniform_jump.json", family="s3")).read_text())
        self.assertGreater(Value(verify_uniform_after_sqrt2(case)) - B, Value(Q("0.011685187")))

    def test_missing_pattern_rejected(self):
        cover = copy.deepcopy(self.cover)
        cover["patterns"].pop()
        with self.assertRaisesRegex(AssertionError, "Gap or overlap"):
            verify(cover, self.certificate)

    def test_indefinite_matrix_rejected(self):
        certificate = copy.deepcopy(self.certificate)
        certificate["blocks"][0]["matrix"][0][0] = Value(-1).json()
        with self.assertRaises(AssertionError):
            verify(self.cover, certificate)

    def test_wrong_value_field_rejected(self):
        certificate = copy.deepcopy(self.certificate)
        certificate["value_polynomial"][0] += 1
        with self.assertRaises(AssertionError):
            verify(self.cover, certificate)


if __name__ == "__main__":
    unittest.main()
