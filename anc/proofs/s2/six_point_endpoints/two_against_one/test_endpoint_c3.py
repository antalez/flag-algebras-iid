"""Endpoint-specific checks for the c3 discontinuity proof."""
from fractions import Fraction as Q
import json
from pathlib import Path
import unittest

import endpoint_c3 as c3
import endpoint_c4 as c4
from ladder_witness import ladder, uniform_c3
from verify_lower_laws import verify_law
from search import events, exact_value

RESULTS = Path(__file__).parent/'results'


class C3EndpointTests(unittest.TestCase):
    def test_shared_engine_keeps_both_polynomials_separate(self):
        for engine in (c3, c4, c3):
            interval = engine.isolate()
            self.assertEqual(engine.sign_at_root(engine.POLY, interval), 0)
            self.assertEqual(engine.sign_at_root([-1, 1], interval), 1)
        self.assertNotEqual(c3.isolate(), c4.isolate())
        with self.assertRaises(ValueError):
            c4.verify_endpoint(json.loads((RESULTS/'sdp6_thresholds/c783186638633_500000000000/cover.json').read_text()),
                               json.loads((RESULTS/'c3_endpoint_cover.json').read_text()))

    def test_uniform_law_near_root_and_at_sample(self):
        law = json.loads((RESULTS/'c3_cplus_witness.json').read_text())
        lo, hi, den = c3.isolate()
        value = Q(law['recursive_lower_bound_exact'])
        for c in (Q(hi, den), Q(law['c'])):
            checked = uniform_c3(Q(lo, den), c, law)
            self.assertEqual(Q(checked['value_exact']), value)
            self.assertEqual(checked['selected_ordered_successes'], 45)
            xs, _ = ladder(c, 3)
            terms, slack = events(xs, c)
            masses = list(map(Q, law['masses_exact']))
            f = exact_value(terms, masses)
            self.assertEqual(f/(1-masses[0]**3), value)
            rho = min(slack/4, xs[1]/(2*c), Q(1, 2))
            generated = dict(support_exact=list(map(str, xs)), masses_exact=law['masses_exact'],
                             base_exact=str(f), value_exact=str(value), rho_exact=str(rho))
            self.assertTrue(verify_law(c, generated)['exact_checked'])

    def test_uniform_law_rejects_wrong_value_and_bracket(self):
        law = json.loads((RESULTS/'c3_cplus_witness.json').read_text())
        cminus, cplus = Q('1.566373277266'), Q(law['c'])
        with self.assertRaises(ValueError):
            uniform_c3(cplus, cplus, law)
        law['recursive_lower_bound_exact'] = '1/2'
        with self.assertRaises(ValueError):
            uniform_c3(cminus, cplus, law)

    def test_endpoint_rejects_missing_branch_and_negative_ray(self):
        data = json.loads((RESULTS/'sdp6_thresholds/c783186638633_500000000000/cover.json').read_text())
        proof = json.loads((RESULTS/'c3_endpoint_cover.json').read_text())
        ray = proof['rays'][0]
        self.assertTrue(c3.verify_ray(ray, c3.isolate()))
        bad = dict(ray, weights=[[-v for v in w] for w in ray['weights']])
        with self.assertRaises(ValueError):
            c3.verify_ray(bad, c3.isolate())
        proof['pruned'].pop(next(iter(proof['pruned'])))
        proof['rays'] = []
        with self.assertRaises(ValueError):
            c3.verify_endpoint(data, proof)


if __name__ == '__main__':
    unittest.main()
