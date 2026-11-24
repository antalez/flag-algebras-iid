"""Exact arithmetic and sign regression tests for the quotient presentation."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
import unittest
from fractions import Fraction as Q
from itertools import product
from quadratic_tower import make_tower,extend_positive


class TowerTests(unittest.TestCase):
    def setUp(self):
        self.F=make_tower(3,2,1)
        self.u=self.F([0,1,0,0]);self.v=self.F([0,0,1,0])

    def test_defining_relations(self):
        self.assertEqual(self.u**2,3)
        self.assertEqual(self.v**2,2+self.u)
        self.assertEqual((self.u+self.v)**2,5+self.u+2*self.u*self.v)

    def test_inverse_and_order(self):
        for coeff in product([-1,0,1],repeat=4):
            x=self.F(coeff)
            if not x:continue
            self.assertEqual(x/x,1)
            self.assertGreater(x*x,0)
            self.assertEqual(x.sign(),x.inverse().sign())

    def test_nested_signs(self):
        self.assertGreater(self.u,Q(17,10))
        self.assertLess(self.u,Q(18,10))
        self.assertGreater(self.v,Q(19,10))
        self.assertLess(self.v,2)
        self.assertGreater(self.v-self.u,0)
        self.assertLess(self.v-self.u-1,0)

    def test_invalid_radical(self):
        with self.assertRaises(AssertionError):make_tower(3,1,-1)

    def test_third_extension(self):
        G=extend_positive(self.F,self.F(7))
        u=G(self.u);v=G(self.v);w=G([0,0,0,0,1,0,0,0])
        self.assertEqual(u*u,3);self.assertEqual(v*v,2+u);self.assertEqual(w*w,7)
        for value in [1+u+v+w,1-u+v-w,3*u-2*v+w]:
            self.assertEqual(value/value,1)
            self.assertGreater(value*value,0)
        self.assertGreater(w,2);self.assertLess(w,3)


if __name__=='__main__':unittest.main()
