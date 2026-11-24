"""Checks for the c2 specialization of the shared algebraic proof engine."""
import copy
from fractions import Fraction as Q
import json
from pathlib import Path
import unittest

import endpoint_c2 as c2
import endpoint_c3 as c3
import endpoint_c4 as c4
from ladder_witness import ladder, uniform_c2
from verify_lower_laws import verify_law
from search import events, exact_value


class C2EndpointTests(unittest.TestCase):
    def test_polynomial_specializations_stay_separate(self):
        intervals = []
        for engine in (c2, c3, c4, c2):
            interval = engine.isolate()
            self.assertEqual(engine.sign_at_root(engine.POLY, interval), 0)
            self.assertEqual(engine.sign_at_root([-1, 1], interval), 1)
            intervals.append(interval)
        self.assertEqual(intervals[0], intervals[-1])
        self.assertEqual(len(set(intervals)), 3)

    def test_saved_ray_and_negative_corruption(self):
        path = Path(__file__).parent/'results/c2_endpoint_cover.json'
        proof = json.loads(path.read_text())
        ray = proof['rays'][0]
        self.assertTrue(c2.verify_ray(ray, c2.isolate()))
        bad = copy.deepcopy(ray)
        bad['weights'] = [[-v for v in w] for w in bad['weights']]
        with self.assertRaises(ValueError):
            c2.verify_ray(bad, c2.isolate())


    def test_uniform_lower_near_root_and_at_sample(self):
        path = Path(__file__).parent/'results/c2_cplus_witness.json'
        law = json.loads(path.read_text())
        lo, hi, den = c2.isolate()
        expected = Q(law['value_exact'])
        for c in (Q(hi, den), Q(law['c'])):
            checked = uniform_c2(Q(lo, den), c, law)
            self.assertEqual(Q(checked['value_exact']), expected)
            self.assertEqual(checked['selected_ordered_successes'], 25)
            xs, _ = ladder(c, 2)
            terms, slack = events(xs, c)
            masses = list(map(Q, law['masses_exact']))
            f = exact_value(terms, masses)
            self.assertEqual(f/(1-masses[0]**3), expected)
            generated = dict(support_exact=list(map(str, xs)), masses_exact=law['masses_exact'],
                             base_exact=str(f), value_exact=str(expected),
                             rho_exact=str(min(slack/4, xs[1]/(2*c), Q(1, 2))))
            self.assertTrue(verify_law(c, generated)['exact_checked'])

    def test_uniform_lower_rejects_corruption(self):
        path = Path(__file__).parent/'results/c2_cplus_witness.json'
        law = json.loads(path.read_text())
        cminus, cplus = Q('1.52137'), Q(law['c'])
        with self.assertRaises(ValueError):
            uniform_c2(cplus, cplus, law)
        bad = dict(law, value_exact='1/2')
        with self.assertRaises(ValueError):
            uniform_c2(cminus, cplus, bad)
        bad = dict(law, masses_exact=['1','0','0','0'])
        with self.assertRaises(ValueError):
            uniform_c2(cminus, cplus, bad)


if __name__ == '__main__':
    unittest.main()
