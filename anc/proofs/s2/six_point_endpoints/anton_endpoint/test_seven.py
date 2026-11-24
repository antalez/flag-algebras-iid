import json
from itertools import combinations
from pathlib import Path
import unittest

from seven_sdp import np, root_block, root_scores


class SevenTests(unittest.TestCase):
    def test_root_normalization_and_matrix_pairing(self):
        states = np.random.default_rng(73).integers(0, 4, size=(30, 35), dtype=np.uint8)
        block = root_block(states)
        multiplicities = np.array([1 if i == j else 2 for i, j in block["pairs"]])
        np.testing.assert_array_equal(block["counts"].T @ multiplicities, np.full(30, 140))
        factor = np.arange(16*3).reshape(16, 3)-23
        q = factor @ factor.T
        coefficients = np.array([q[i, j]*(1 if i == j else 2) for i, j in block["pairs"]])
        np.testing.assert_array_equal(block["counts"].T @ coefficients, root_scores(states, q))
        np.testing.assert_allclose(root_scores(states, q.astype(float)), root_scores(states, q)/140)

    def test_saved_restrictions_and_objective(self):
        path = Path(__file__).with_name("results")
        if not (path/"cover7.npz").exists():
            self.skipTest("No saved seven-point cover")
        archive = np.load(path/"cover7.npz")
        selected = np.random.default_rng(41).choice(len(archive["states"]), 100, replace=False)
        states, restrictions = archive["states"][selected], archive["restrictions"][selected]
        six = archive["states6"]
        fours = list(combinations(range(7), 4))
        for j, vertices in enumerate(combinations(range(7), 6)):
            indices = [fours.index(tuple(vertices[i] for i in t)) for t in combinations(range(6), 4)]
            np.testing.assert_array_equal(states[:, indices], six[restrictions[:, j]])
        np.testing.assert_allclose(states.sum(axis=1)/140, (six.sum(axis=1)/60)[restrictions].mean(axis=1))
        cover = json.loads((path/"cover6.json").read_text())
        np.testing.assert_array_equal(six.sum(axis=1), [p.count("+") for p in cover["patterns"]])


if __name__ == "__main__":
    unittest.main()
