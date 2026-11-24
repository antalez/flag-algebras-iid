from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import unittest

from quadratic import Q2, solve_linear
from enumerate_patterns import candidates, gap_rows, verify_cover


class EndpointTests(unittest.TestCase):
    def test_field_and_order(self):
        c = Q2(1, 1)
        self.assertEqual(c*c, 2*c+1)
        self.assertEqual((Q2(1)/c)*c, Q2(1))
        for a, b in product(range(-10, 11), repeat=2):
            x = Q2(a, b)
            numeric = float(x)
            self.assertEqual(x.sign(), (numeric > 0)-(numeric < 0))

    def test_exact_linear_solve(self):
        result = solve_linear([[Q2(1), Q2(0, 1)], [Q2(0, 1), Q2(1)]], [Q2(3), Q2(2)])
        self.assertEqual(result[0]+Q2(0, 1)*result[1], Q2(3))
        self.assertEqual(Q2(0, 1)*result[0]+result[1], Q2(2))

    def test_endpoint_specific_conflict(self):
        rows = gap_rows(5, [(0, 2, 3, 1), (1, 2, 4, 3)], Q2(1, 1))
        certificate = [Q2(0, 1)*a+b for a, b in zip(*rows)]
        self.assertTrue(all(v.sign() >= 0 for v in certificate))
        self.assertTrue(any(not v for v in certificate))

    def test_five_point_cover_and_metadata(self):
        path = Path(__file__).with_name("results") / "cover5.json"
        data = json.loads(path.read_text())
        self.assertTrue(verify_cover(data))
        self.assertEqual(len(data["patterns"]), 52)
        data["coefficient"] = ["2", "0"]
        with self.assertRaises(ValueError):
            verify_cover(data)


if __name__ == "__main__":
    unittest.main()
