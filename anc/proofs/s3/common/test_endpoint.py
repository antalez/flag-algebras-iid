"""Proof checks and rejected corruptions for the exact S3 endpoint."""

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
import unittest

from endpoint_cover import C, Endpoint, HERE, verify_cover
from endpoint_field import Value, B, Z
from verify_endpoint import verify


class EndpointTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cover = json.loads((data_path("endpoint_n4_cover.json", family="s3")).read_text())
        cls.certificate = json.loads((data_path("endpoint_n4_field_certificate.json", family="s3")).read_text())

    def test_correct_algebraic_roots(self):
        self.assertTrue(Q("2.302775637731994") < C < Q("2.302775637731995"))
        self.assertTrue(Q("0.3963799474937") < Z < Q("0.3963799474938"))
        self.assertTrue(Q("0.4827817466286") < B < Q("0.4827817466287"))

    def test_missing_pattern_rejected(self):
        cover = copy.deepcopy(self.cover)
        cover["patterns"].pop()
        with self.assertRaisesRegex(AssertionError, "Gap or overlap"):
            verify_cover(cover)

    def test_negative_gordan_weight_rejected(self):
        cover = copy.deepcopy(self.cover)
        proof = next(iter(cover["pruned"].values()))
        proof[next(iter(proof))] = Endpoint(-1).json()
        with self.assertRaises(AssertionError):
            verify_cover(cover)

    def test_indefinite_matrix_rejected(self):
        certificate = copy.deepcopy(self.certificate)
        certificate["blocks"][0]["matrix"][0][0] = Value(-1).json()
        with self.assertRaisesRegex(AssertionError, "nonpositive exact LDL"):
            verify(self.cover, certificate)

    def test_excessive_positive_matrix_perturbation_rejected(self):
        certificate = copy.deepcopy(self.certificate)
        old = Value(certificate["blocks"][0]["matrix"][0][0])
        certificate["blocks"][0]["matrix"][0][0] = (old + 1000).json()
        with self.assertRaisesRegex(AssertionError, "Scores exceed"):
            verify(self.cover, certificate)

    def test_certificate_proves_plateau(self):
        result = verify(self.cover, self.certificate)
        self.assertTrue(result["exact_plateau_proved"])
        self.assertTrue(result["all_exact_checks_passed"])
        self.assertFalse(result["near_optimality_constraints_used"])


if __name__ == "__main__":
    unittest.main()
