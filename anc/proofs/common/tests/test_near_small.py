"""Regression checks that the exact near-optimal verifier rejects corrupt proofs."""

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

from verify_near_small import verify_near
from verify_second_plateau import verify_exact

HERE = Path(__file__).resolve().parent


class NearCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cover = json.loads((data_path('near_c2_exact_cover.json', family="s2")).read_text())
        cls.cert = json.loads((data_path('near_c2_certificate.json', family="s2")).read_text())

    def test_valid_certificate(self):
        result = verify_near(self.cover, self.cert)
        self.assertLess(result['gap_from_lower'], 1.3e-9)
        self.assertTrue(result['lower_witness_verified'])

    def test_negative_multiplier(self):
        cert = copy.deepcopy(self.cert)
        cert['multipliers'][0] = '-1'
        with self.assertRaises(AssertionError):
            verify_near(self.cover, cert)

    def test_falsified_upper(self):
        cert = copy.deepcopy(self.cert)
        cert['upper'] = cert['lower']
        with self.assertRaises(AssertionError):
            verify_near(self.cover, cert)

    def test_invalid_lower_witness(self):
        cert = copy.deepcopy(self.cert)
        cert['lower_witness']['masses'][0] = '0'
        with self.assertRaises(AssertionError):
            verify_near(self.cover, cert)

    def test_zero_gap_identity_is_not_plateau_certificate(self):
        start=2*(1+2*len(self.cover['cuts']))
        count=start+4*(len(self.cover['cuts'])+1)
        multipliers=[['0','0'] for _ in range(count)]
        for j in range(start+1,count,2):multipliers[j]=['1','0']
        identity=dict(blocks=[],multipliers=multipliers,full_near_optimality=True)
        with self.assertRaises(AssertionError):
            verify_exact(self.cover,identity,minimum_margin=0)


if __name__ == '__main__':
    unittest.main()
