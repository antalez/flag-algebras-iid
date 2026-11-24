"""Independent event counting and recursion checks for the new search."""
from fractions import Fraction as Q
from itertools import product
from math import sqrt
import json
from pathlib import Path
import unittest

from search import events, exact_value, optimize, tuples
from three_atom_cells import cells


def brute(support, masses, c):
    return sum((masses[i]*masses[j]*masses[k]
                for i, j, k in product(range(len(support)), repeat=3)
                if support[i]+support[j] < c*support[k]), Q(0))


class SearchTests(unittest.TestCase):
    def test_saved_certificates(self):
        files = list((Path(__file__).parent/"results").rglob("*.json"))
        self.assertTrue(files)
        for path in files:
            data = json.loads(path.read_text())
            if "c" not in data:
                continue
            c = Q(data["c"])
            if "selected" in data:
                xs = list(map(Q, data["x_exact"]))
                self.assertTrue(all(c*xs[k] > xs[i]+xs[j] for i, j, k in data["selected"]))
                self.assertTrue(all(c*xs[k]-xs[i]-xs[j] >= Q(str(data["margin"]))
                                    for i, j, k in data["selected"]))
                if data["mode"] == "distinct":
                    self.assertEqual(len(data["selected"]), data["objective"])
                    self.assertEqual(len(set(map(tuple, data["selected"]))), data["objective"])
                else:
                    self.assertEqual(sum(1 if i == j else 2 for i, j, k in data["selected"]), data["objective"])
                empirical = brute(xs, [Q(1, len(xs))]*len(xs), c)
                self.assertEqual(empirical, Q(data["empirical_iid_exact"]))
            for law in data.get("laws", []):
                support = list(map(Q, law["support_exact"]))
                masses = list(map(Q, law["masses_exact"]))
                self.assertEqual(sum(masses), 1)
                self.assertTrue(all(p >= 0 for p in masses))
                f = brute(support, masses, c)
                self.assertEqual(f, Q(law["base_exact"]))
                self.assertEqual(f/(1-masses[0]**3), Q(law["value_exact"]))
                _, d = events(support, c)
                rho = Q(law["rho_exact"])
                self.assertTrue(0 < 2*rho < d and c*rho < support[1])

    def test_tuple_objectives(self):
        xs = list(map(Q, [0, 0, 1, 2, 3, 4]))
        c = Q(3, 2)
        ts, weights, den = tuples(len(xs), "iid")
        count = sum(w for (i, j, k), w in zip(ts, weights) if xs[i]+xs[j] < c*xs[k])
        self.assertEqual(Q(count, den), brute(xs, [Q(1, 6)]*6, c))
        ts, weights, den = tuples(len(xs), "distinct")
        count = sum(xs[i]+xs[j] < c*xs[k] for i, j, k in ts)
        ordered = [(i, j, k) for i, j, k in product(range(6), repeat=3)
                   if len({i, j, k}) == 3]
        direct = sum(xs[i]+xs[j] < c*xs[k] for i, j, k in ordered)
        self.assertEqual(Q(count, den), Q(direct, len(ordered)))

    def test_small_margin_artifact(self):
        c = Q("1.41422")
        a = (1/c+c/2)/2
        rho = min(c*a-1, c-2*a)/10
        xs = [Q(0)]*2+[rho*a]*2+[rho]+[a]*5+[Q(1)]*2
        ts, _, _ = tuples(12, "distinct")
        slacks = [c*xs[k]-xs[i]-xs[j] for i, j, k in ts if c*xs[k] > xs[i]+xs[j]]
        self.assertEqual(len(slacks), 316)
        self.assertLess(min(slacks), Q("2e-7"))

    def test_simple_law_at_185(self):
        c = Q("1.85")
        support = list(map(Q, ["0", ".55", ".84", "1"]))
        masses = list(map(Q, [".225134", ".204448", ".241087", ".329331"]))
        self.assertEqual(sum(masses), 1)
        f = brute(support, masses, c)
        self.assertEqual(f/(1-masses[0]**3), Q(14539159688963109, 26718621935872808))
        _, d = events(support, c)
        rho = Q(1, 1000)
        self.assertTrue(2*rho < d and c*rho < support[1])
        expanded_s = [rho*v for v in support]+support[1:]
        expanded_m = [masses[0]*p for p in masses]+masses[1:]
        self.assertEqual(brute(expanded_s, expanded_m, c), f*(1+masses[0]**3))

    def test_recursive_construction(self):
        c = Q("1.5213")
        s = list(map(Q, ["0", "0.3", "0.71", "1"]))
        masses = list(map(Q, ["0.4", "0.1", "0.3", "0.2"]))
        terms, d = events(s, c)
        f = exact_value(terms, masses)
        self.assertEqual(f, brute(s, masses, c))
        rho = min(d/4, s[1]/(2*c), Q(1, 2))
        # Replace the zero once, retaining a final zero atom.
        expanded_s = [rho*v for v in s]+s[1:]
        expanded_m = [masses[0]*p for p in masses]+masses[1:]
        self.assertEqual(brute(expanded_s, expanded_m, c), f*(1+masses[0]**3))

    def test_known_values(self):
        below = optimize(list(map(Q, ["0", ".71", "1"])), Q("1.52"), 4)
        self.assertAlmostEqual(below["value"], (2*sqrt(403)-28)/27, places=11)
        above = optimize(list(map(Q, ["0", ".6576", ".8642", "1"])), Q("1.522"), 4)
        beta = 1/(3*sqrt(3))
        k = 1-beta
        value = 2/3*(sqrt(9*k*k-3*k+1)-3*k+1)
        self.assertAlmostEqual(above["value"], value, places=11)

    def test_cells_and_threshold(self):
        c = Q("1.5213797")
        self.assertLess(c**3-c-2, 0)
        supports = cells(c)
        self.assertEqual(len(supports), 31)
        patterns = set()
        for s in supports:
            self.assertTrue(0 < s[1] < s[2] < 1)
            pattern = tuple(c*s[k] > s[i]+s[j] for i, j, k in product(range(4), repeat=3))
            self.assertNotIn(pattern, patterns)
            patterns.add(pattern)


if __name__ == "__main__":
    unittest.main()
