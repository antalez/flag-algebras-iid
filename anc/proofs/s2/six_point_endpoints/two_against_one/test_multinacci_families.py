"""Exact tests of the new analytic lower-family constructions."""
from fractions import Fraction as Q
from itertools import product
import json
import copy
from pathlib import Path
import unittest

from multinacci_families import (evaluate, root_bracket, multinacci_polynomial,
    intermediate_polynomial, LIMIT_POLYNOMIAL, multinacci_support,
    intermediate_support, limit_support, selected_success, selected_terms, verify_uniform_family)
from verify_lower_laws import verify_law
from search import exact_value


class FamilyTests(unittest.TestCase):
    def test_multinacci_events_near_every_root(self):
        for m in range(1, 7):
            poly = multinacci_polynomial(m)
            lo, hi = root_bracket(poly, bits=256)
            c = hi+Q(1, 2**256)
            xs = multinacci_support(c, m)
            self.assertTrue(all(a < b for a, b in zip(xs, xs[1:])))
            for i, j, k in product(range(len(xs)), repeat=3):
                self.assertEqual(xs[i]+xs[j] < c*xs[k], min(i, j) < k)
            with self.assertRaises(ValueError):
                multinacci_support(lo, m)

    def test_intermediate_events_near_roots_and_farther_right(self):
        for n in range(7):
            poly = intermediate_polynomial(n)
            lo, hi = root_bracket(poly, bits=256)
            for c in (hi+Q(1, 2**256), Q('1.99')):
                xs = intermediate_support(c, n)
                self.assertTrue(all(a < b for a, b in zip(xs, xs[1:])))
                self.assertGreater(c*xs[1], 1)
                self.assertLess(xs[-2]+1, c)
                for j in range(1, n+1):
                    self.assertLess(xs[1]+xs[j], c*xs[j+1])
                for i, j, k in product(range(len(xs)), repeat=3):
                    if selected_success('intermediate', i, j, k, len(xs)-1):
                        self.assertLess(xs[i]+xs[j], c*xs[k])
                self.assertEqual(sum(selected_terms('intermediate', len(xs)).values()),
                                 4*n*n+13*n+13)
            with self.assertRaises(ValueError):
                intermediate_support(lo, n)

    def test_intermediate_roots_increase_to_the_correct_limit(self):
        self.assertEqual(intermediate_polynomial(1), [-2, 0, -1, 1])
        self.assertEqual(intermediate_polynomial(2), [-2, -1, 0, -1, 1])
        previous = root_bracket(multinacci_polynomial(2))[1]
        limit_lo, limit_hi = root_bracket(LIMIT_POLYNOMIAL)
        for n in range(1, 9):
            lo, hi = root_bracket(intermediate_polynomial(n))
            self.assertLess(previous, lo)
            self.assertLess(hi, limit_lo)
            previous = hi
            c = Q(7, 4)
            self.assertEqual((c-1)*evaluate(intermediate_polynomial(n), c),
                             c**n*(c*(c-1)**2-1)-(c-2))
        self.assertLess(limit_hi, root_bracket(multinacci_polynomial(3))[0])

    def test_limit_family(self):
        lo, hi = root_bracket(LIMIT_POLYNOMIAL, bits=256)
        c = hi+Q(1, 2**256)
        xs = limit_support(c)
        self.assertLess(1/c, xs[1])
        self.assertLess(xs[1]+xs[2], c*xs[2])
        self.assertLess(xs[2]+1, c)
        for i, j, k in product(range(4), repeat=3):
            if selected_success('limit', i, j, k, 3):
                self.assertLess(xs[i]+xs[j], c*xs[k])
        self.assertEqual(sum(selected_terms('limit', 4).values()), 32)
        with self.assertRaises(ValueError):
            limit_support(lo)

    def test_saved_rational_lower_probabilities(self):
        path = Path(__file__).parent/'results/multinacci_families.json'
        rows = json.loads(path.read_text())['rows']
        for row in rows:
            law = row['sampled_law']
            checked = verify_law(Q(row['c']), law)
            masses = list(map(Q, law['masses_exact']))
            terms = selected_terms(row['family'], len(masses))
            f = exact_value(terms, masses)
            self.assertEqual(str(f), row['selected_base_exact'])
            self.assertEqual(f/(1-masses[0]**3), Q(row['uniform_right_lower_exact']))
            self.assertLessEqual(Q(row['uniform_right_lower_exact']), Q(checked['exact_lower']))


    def test_uniform_family_verifier_and_corruption(self):
        path = Path(__file__).parent/'results/multinacci_families.json'
        rows = json.loads(path.read_text())['rows']
        for row in rows:
            checked = verify_uniform_family(row)
            self.assertEqual(checked['value_exact'], row['uniform_right_lower_exact'])
            bad = copy.deepcopy(row)
            bad['polynomial'][0] += 1
            with self.assertRaises(ValueError):
                verify_uniform_family(bad)
            bad = dict(row, uniform_right_lower_exact='1')
            with self.assertRaises(ValueError):
                verify_uniform_family(bad)






if __name__ == '__main__':
    unittest.main()
