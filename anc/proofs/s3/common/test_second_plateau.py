"""Meaningful checks of the second plateau's field, PSD and proof rejection."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from anc.proofs.paths import data_path
import copy
import json
from pathlib import Path
import unittest

from second_plateau_field import Value, Z, A, D, B, positive_definite
from verify_second_plateau import verify

HERE = Path(__file__).resolve().parent


class SecondPlateauTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cover = json.loads((data_path("n4_c47-20_cuts47-40_60-47_27-20_47-27_47-20_cover.json", family="s3")).read_text())
        cls.certificate = json.loads((data_path("second_plateau_n4_field_certificate.json", family="s3")).read_text())

    def test_mass_normalization_and_decimal_stability(self):
        self.assertEqual(Z + A + D, Value(1))
        self.assertTrue(0 < Z < 1 and A > 0 and D > 0)
        self.assertAlmostEqual(float(Z), 0.3767059973499557, places=14)
        self.assertAlmostEqual(float(B), 0.49115608181379744, places=14)
        n = (A * (Z ** 3 + 3 * Z ** 2 * (A + D) + 3 * Z * (A ** 2 + 2 * A * D))
             + D * (Z ** 3 + 3 * Z ** 2 * (A + D) + 3 * Z * (A + D) ** 2 + A ** 3))
        self.assertEqual(B, n / (1 - Z ** 4))

    def test_rigorous_psd_enclosures(self):
        self.assertTrue(positive_definite([[2, Z], [Z, 1]]))
        # All diagonal entries are positive, but the determinant is negative.
        self.assertLess(Z * D - A * A, Value(0))
        with self.assertRaises(AssertionError):
            positive_definite([[Z, A], [A, D]])

    def test_missing_pattern_rejected(self):
        cover = copy.deepcopy(self.cover)
        cover["patterns"].pop()
        with self.assertRaises(AssertionError):
            verify(cover, self.certificate)

    def test_indefinite_certificate_rejected(self):
        certificate = copy.deepcopy(self.certificate)
        certificate["blocks"][0]["matrix"][0][0] = Value(-1).json()
        with self.assertRaises(AssertionError):
            verify(self.cover, certificate)

    def test_full_exact_certificate(self):
        result = verify(self.cover, self.certificate)
        expected = json.loads((data_path("second_plateau_n4_verification.json", family="s3")).read_text())
        self.assertEqual(result, expected)
        self.assertEqual(result["tight_patterns"], 120)
        self.assertEqual(result["interval"], "(1+sqrt(13))/2<c<=47/20")
        self.assertTrue(result["exact_plateau_proved"])


if __name__ == "__main__":
    unittest.main()
