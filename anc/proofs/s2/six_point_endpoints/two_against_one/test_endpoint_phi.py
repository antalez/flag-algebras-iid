"""Exact checks for the phi lower family and endpoint ray reconstruction."""
from fractions import Fraction as Q
import json
from pathlib import Path
import unittest
import numpy as np
from scipy import sparse
from refine_sdp6 import FactorObjective

import endpoint_phi as phi
import endpoint_c2 as c2
from endpoint_c4 import reconstruct_with_alternatives
from ladder_witness import phi_support, uniform_phi
from search import events, exact_value
from verify_lower_laws import verify_law

RESULTS = Path(__file__).parent/'results'


class PhiTests(unittest.TestCase):
    def test_distinct_root_and_exact_polynomial_reduction(self):
        interval = phi.isolate()
        self.assertEqual(phi.sign_at_root(phi.POLY, interval), 0)
        self.assertEqual(phi.sign_at_root([-1, 1], interval), 1)
        self.assertNotEqual(interval, c2.isolate())

    def test_lower_family_arbitrarily_close_from_right(self):
        law = json.loads((RESULTS/'phi_cplus_witness.json').read_text())
        lo, hi, den = phi.isolate()
        for c in (Q(hi, den), Q(law['c'])):
            xs = phi_support(c)
            checked = uniform_phi(Q(lo, den), c, law)
            self.assertEqual(checked['selected_ordered_successes'], 13)
            terms, slack = events(xs, c)
            masses = list(map(Q, law['masses_exact']))
            f = exact_value(terms, masses)
            self.assertEqual(f/(1-masses[0]**3), Q(law['value_exact']))
            generated = dict(support_exact=list(map(str, xs)), masses_exact=law['masses_exact'],
                             base_exact=str(f), value_exact=law['value_exact'],
                             rho_exact=str(min(slack/4, xs[1]/(2*c), Q(1, 2))))
            self.assertTrue(verify_law(c, generated)['exact_checked'])
        self.assertGreater(Q(law['value_exact']), Q(1, 2))
        with self.assertRaises(ValueError):
            phi_support(Q(lo, den))

    def test_lower_rejects_wrong_bracket_and_value(self):
        law = json.loads((RESULTS/'phi_cplus_witness.json').read_text())
        cplus, cminus = Q(law['c']), Q('1.618023988749')
        with self.assertRaises(ValueError):
            uniform_phi(cplus, cplus, law)
        law['value_exact'] = '1/2'
        with self.assertRaises(ValueError):
            uniform_phi(cminus, cplus, law)

    def test_alternative_supports_verify_all_branch_signs(self):
        path = RESULTS/'sdp6_phi_clean/c1618023988749_1000000000000/cover.json'
        data = json.loads(path.read_text())
        for pattern in ('++++++++++++++++++++-++-++-+',
                        '++++++++++++++++++++--+--+--+-+',
                        '++++++++++++++++-----++-++--+---+++'):
            ray = reconstruct_with_alternatives(6, pattern, data['pruned'][pattern],
                Q(data['coefficient'][0]), phi.isolate(), polynomial=phi.POLY)
            self.assertTrue(phi.verify_ray(ray, phi.isolate()))
            for i, sign in zip(ray['events'], ray['signs']):
                self.assertEqual(pattern[i], '+' if sign == 1 else '-')


    def test_six_point_factor_gradient(self):
        rng = np.random.default_rng(528)
        blocks = []
        for n in (2, 3):
            pairs = [(i, j) for j in range(n) for i in range(j+1)]
            blocks.append(dict(flags=[None]*n, pairs=pairs,
                               operator=sparse.csc_matrix(rng.normal(size=(len(pairs), 4)))))
        function = FactorObjective(rng.normal(size=4), blocks, .3)
        x = rng.normal(size=13)
        _, gradient = function(x)
        direction = rng.normal(size=len(x))
        step = 1e-6
        finite = (function(x+step*direction)[0]-function(x-step*direction)[0])/(2*step)
        self.assertAlmostEqual(finite, gradient @ direction, places=6)


if __name__ == '__main__':
    unittest.main()
