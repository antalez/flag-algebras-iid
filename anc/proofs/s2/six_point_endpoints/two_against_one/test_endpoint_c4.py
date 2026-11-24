"""Exact checks for polynomial endpoint Farkas certificates."""
import copy
from fractions import Fraction as Q
from itertools import permutations
import json
from math import factorial
from pathlib import Path
import random
import unittest

from endpoint_c4 import (POLY, add, linear_product, determinant,
    determinant_polynomial, isolate, sign_at_root, reconstruct, verify_ray, verify_endpoint)


def brute_determinant(matrix):
    n = len(matrix)
    total = 0
    for p in permutations(range(n)):
        inversions = sum(p[i] > p[j] for i in range(n) for j in range(i+1, n))
        term = (-1)**inversions
        for i, j in enumerate(p):
            term *= matrix[i][j]
        total += term
    return total


class EndpointTests(unittest.TestCase):
    def test_integer_determinants_with_pivots(self):
        rng = random.Random(407)
        for n in range(1, 6):
            for _ in range(12):
                matrix = [[rng.randrange(-3, 4) for _ in range(n)] for _ in range(n)]
                self.assertEqual(determinant(matrix), brute_determinant(matrix))

    def test_polynomial_interpolation_at_rational_points(self):
        rng = random.Random(408)
        for n in range(1, 5):
            matrix = [[(rng.randrange(-3, 4), rng.randrange(-3, 4))
                       for _ in range(n)] for _ in range(n)]
            polynomial = determinant_polynomial(matrix)
            for c in (Q(7, 5), Q(-2, 3)):
                actual = sum(v*c**j for j, v in enumerate(polynomial))
                expected = factorial(n)*brute_determinant([[a+b*c for a, b in row] for row in matrix])
                self.assertEqual(actual, expected)

    def test_algebraic_signs_and_zero_reduction(self):
        interval = isolate()
        self.assertEqual(sign_at_root(POLY, interval), 0)
        self.assertEqual(sign_at_root([-4, 0, 0, 1], interval), 1)
        for value in (-7, 0, 4):
            polynomial = add(linear_product(POLY, 11, -5), [value])
            self.assertEqual(sign_at_root(polynomial, interval), (value > 0)-(value < 0))

    def test_near_zero_seed_slacks_and_corruption(self):
        folder = Path(__file__).parent/'results'
        path = folder/'sdp7_c4_global/cover6.json'
        if not path.exists():
            self.skipTest('Saved pruning rays unavailable')
        data = json.loads(path.read_text())
        pattern = '+++++++++++++++++++++++-++-------------+'
        ray = reconstruct(6, pattern, data['pruned'][pattern], Q(data['coefficient'][0]),
                          isolate(), tolerance=Q(1, 10**6))
        self.assertTrue(verify_ray(ray, isolate()))
        bad = copy.deepcopy(ray)
        bad['weights'] = [[-v for v in w] for w in bad['weights']]
        with self.assertRaises(ValueError):
            verify_ray(bad, isolate())

    def test_complete_endpoint_cover(self):
        folder = Path(__file__).parent/'results'
        if not (folder/'c4_endpoint_cover.json').exists():
            self.skipTest('Saved endpoint proof unavailable')
        data = json.loads((folder/'sdp7_c4_global/cover6.json').read_text())
        proof = json.loads((folder/'c4_endpoint_cover.json').read_text())
        self.assertTrue(verify_endpoint(data, proof)['exact_endpoint_cover'])
        proof['seven_exclusions'].pop(next(iter(proof['seven_exclusions'])))
        with self.assertRaises(ValueError):
            verify_endpoint(data, proof)


if __name__ == '__main__':
    unittest.main()
