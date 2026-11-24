"""Standard-library regression checks for the exact five-point verifier."""
import copy,json,random,unittest
from field import F,R,BSTAR,positive_definite
from verify_field_certificate import verify,HERE

class CertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cert=json.loads((HERE/'n5_field_certificate.json').read_text())
        cls.cover=json.loads((HERE/'n5_cut2_exact_cover.json').read_text())
    def test_field_identities(self):
        self.assertEqual(R**4-4*R**3-3*R**2-2*R+2,F(0))
        self.assertEqual(16*BSTAR**4+8*BSTAR**3+99*BSTAR**2-32*BSTAR-4,F(0))
        self.assertTrue(0<R<1)
        self.assertGreater((R-F('1/2'))**2,0)
        rng=random.Random(17)
        for _ in range(20):
            a=F([rng.randrange(-8,9) for _ in range(4)])
            if a:self.assertEqual(a*(1/a),F(1))
    def test_positive_definiteness(self):
        self.assertTrue(positive_definite([[F(2),R],[R,F(1)]]))
        with self.assertRaises(AssertionError):positive_definite([[F(1),F(2)],[F(2),F(1)]])
    def test_certificate(self):
        report=verify(self.cert,self.cover)
        self.assertTrue(report['proves_equality'])
        self.assertEqual(report['tight_patterns'],33)
    def test_corruption_rejected(self):
        for case in ('missing_pattern','negative_multiplier','indefinite_matrix','wrong_multiplier'):
            with self.subTest(case=case):
                cert=copy.deepcopy(self.cert);cover=copy.deepcopy(self.cover)
                if case=='missing_pattern':cover['patterns'].pop()
                elif case=='negative_multiplier':cert['multipliers'][0]=['-1']
                elif case=='indefinite_matrix':cert['blocks'][0]['matrix'][0][0]=['-1000000']
                else:
                    from fractions import Fraction
                    cert['multipliers'][0]=[str(Fraction(cert['multipliers'][0][0])+1)]
                with self.assertRaises(AssertionError):verify(cert,cover)

if __name__=='__main__':unittest.main()
