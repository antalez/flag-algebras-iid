"""Check the c4 law, recursion, and behavior arbitrarily near its threshold."""
from fractions import Fraction as Q
from itertools import product, combinations
import json
from pathlib import Path
import unittest

from ladder_witness import ladder, uniform_c4, verify
from sdp6 import bracket


def probability(xs, ps, c):
    return sum((ps[i]*ps[j]*ps[k] for i, j, k in product(range(len(xs)), repeat=3)
                if xs[i]+xs[j] < c*xs[k]), Q(0))


class LadderTests(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((Path(__file__).parent/"results/c4_cplus_witness.json").read_text())
        self.law = self.data["laws"][0]

    def test_exact_recursive_witness(self):
        c = Q(self.data["c"])
        verify(c, self.law)
        xs, ps = [list(map(Q, self.law[key])) for key in ("support_exact", "masses_exact")]
        f = probability(xs, ps, c)
        rho = Q(self.law["rho_exact"])
        self.assertEqual(f, Q(self.law["base_exact"]))
        expanded_xs = [rho*x for x in xs]+xs[1:]
        expanded_ps = [ps[0]*p for p in ps]+ps[1:]
        self.assertEqual(probability(expanded_xs, expanded_ps, c), f*(1+ps[0]**3))

    def test_independent_c3_and_c4_lower_verifier(self):
        from verify_lower_laws import verify_law
        path = Path(__file__).parent/'results/c3_cplus_witness.json'
        c3 = json.loads(path.read_text())
        self.assertTrue(verify_law(Q(c3['c']), c3)['exact_checked'])
        self.assertTrue(verify_law(Q(self.data['c']), self.law)['exact_checked'])
        bad = dict(c3, recursive_lower_bound_exact='1/2')
        with self.assertRaises(ValueError):
            verify_law(Q(c3['c']), bad)

    def test_right_family_near_root(self):
        ps = list(map(Q, self.law["masses_exact"]))
        for epsilon in map(Q, (".00001", ".0000001", ".0000000001")):
            below, above = bracket(4, epsilon)
            with self.assertRaises(ValueError):
                ladder(below, 4)
            xs, delta = ladder(above, 4)
            self.assertGreater(delta, 0)
            self.assertEqual(probability(xs, ps, above)/(1-ps[0]**3), Q(self.law["value_exact"]))
            self.assertTrue(uniform_c4(below, above, self.law)["exact_checked"])

    def test_highs_exact_cover(self):
        import highspy
        # Initialize the shared scheduler through another LP first. Pattern
        # enumeration must coexist with LP solvers in the same process.
        warm = highspy.Highs()
        warm.setOptionValue('output_flag', False)
        warm.addVar(0., 1.)
        warm.run()
        from enumerate_patterns import enumerate_cover, verify_cover
        data = enumerate_cover(4, 30, coefficient=Q(self.data["cminus"]),
                               summands=2, backend="highs")
        self.assertTrue(data["complete"] and verify_cover(data))
        self.assertEqual(len(data["patterns"]), 16)
        self.assertEqual(data["unverified_rays"], 0)

    def test_global_exclusion_rejects_corruption(self):
        from sdp7 import verify_seven_exclusions
        path = Path(__file__).parent/'results/sdp7_c4_global/cover6.json'
        if not path.exists():
            self.skipTest('Saved global pruning proofs unavailable')
        data = json.loads(path.read_text())
        pattern, proof = next(iter(data['seven_exclusions'].items()))
        data['seven_exclusions'] = {pattern: proof}
        self.assertEqual(verify_seven_exclusions(data), {pattern})
        # The all-failure pattern is realizable by constant positive values;
        # no Farkas proof can exclude it.
        data['seven_exclusions'] = {'-'*70: proof}
        with self.assertRaises(ValueError):
            verify_seven_exclusions(data)

    def test_global_signs_agree_with_every_restriction(self):
        import numpy as np
        from sdp7 import global_event_signs, candidates
        folder = Path(__file__).parent/'results/sdp7_c4'
        if not (folder/'cover7.npz').exists():
            self.skipTest('Saved compatible cover unavailable')
        data = json.loads((Path(__file__).parent/'results/sdp6_c4'/
                           'c1588780530011_1000000000000/cover.json').read_text())
        with np.load(folder/'cover7.npz') as a:
            states, restrictions = a['states'][::5000], a['restrictions'][::5000]
        signs = global_event_signs(data, states)
        lookup = {t:i for i,t in enumerate(candidates(7, False, 2))}
        for j, six in enumerate(combinations(range(7), 6)):
            ids = [lookup[tuple(six[i] for i in t)] for t in data['tuples']]
            expected = [[1 if v == '+' else -1 for v in data['patterns'][i]]
                        for i in restrictions[:, j]]
            np.testing.assert_array_equal(signs[:, ids], expected)


if __name__ == "__main__":
    unittest.main()
