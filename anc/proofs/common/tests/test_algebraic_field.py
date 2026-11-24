"""Regression checks for isolated roots and non-monic quotient arithmetic."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
import unittest
from fractions import Fraction as Q
from algebraic_field import make_field
from quadratic_tower import extend_positive


class IsolatedQuinticTest(unittest.TestCase):
    def test_branching_candidate(self):
        field = make_field([-2304, 7040, -576, -11136, 2952, 3753],
                           local_isolation=True)
        x = field([0, 1, 0, 0, 0])
        self.assertEqual(3753*x**5+2952*x**4-11136*x**3-576*x*x+7040*x-2304, 0)
        self.assertTrue(Q(1060454, 10**6) < x < Q(1060457, 10**6))
        a = x/2
        b = -(28841805*a**5+19225611*a**4-16124046*a**3-4953896*a**2+2011200*a)/(16514*a)
        t = (37833993*a**5+25282872*a**4-21120918*a**3-6549752*a**2+2655736*a)/(33028*a)
        d = 1-a-b-t
        self.assertTrue(all(z > 0 for z in (a,b,t,d)))
        self.assertEqual(a+b+t+d, 1)
        self.assertEqual(x/x, 1)
        # Derivatives of the one-scale success polynomial after d=1-a-b-t.
        self.assertEqual(-3*a*a-4*a*b-4*a*t+2*a-3*b*b-2*b*t+2*b-2*t*t+2*t, 0)
        self.assertEqual(-2*a*a-6*a*b-2*a*t+2*a-3*b*b-2*b*t+2*b, 0)
        self.assertEqual(-2*a*a-2*a*b-4*a*t+2*a-b*b, 0)
        beta = a*a*(b+t+d)+2*a*b*(t+d)+2*a*t*d+b*b*d
        k = 1-beta
        extended = extend_positive(field, 1-3*k+9*k*k)
        root = extended([0]*5+[1]+[0]*4)
        k = extended(k)
        self.assertTrue(root > 0)
        self.assertEqual(root*root, 1-3*k+9*k*k)
        w = (1+3*k-root)/(3*k)
        bound = Q(2,3)*(root-3*k+1)
        self.assertTrue(0 < w < 1)
        self.assertEqual((1-k*w*w)/(3-3*w+w*w), bound)

    def test_ambiguous_interval_rejected(self):
        with self.assertRaises(AssertionError):
            make_field([-6, 11, -6, 1], local_isolation=True)


if __name__ == '__main__':
    unittest.main()
