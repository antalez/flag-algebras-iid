"""Independent checks of (3,5) normalization and expanded Gram certificates."""
import contextlib
from fractions import Fraction as Q
import io
from itertools import combinations
import json
from pathlib import Path
import unittest

from expanded_sdp7 import np, assemble, extra_blocks, certify_expanded, block_score
from verify_sdp7 import verify


class ExpandedTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.base = Path(__file__).parent/'results'
        folder = cls.base/'sdp7_c4_global'
        if not (folder/'cover6.json').exists():
            raise unittest.SkipTest('Saved c4 cover unavailable')
        cls.data = json.loads((folder/'cover6.json').read_text())
        empty = cls.data['patterns'].index('-'*len(cls.data['tuples']))
        with np.load(folder/'cover7.npz') as a:
            ids = np.flatnonzero(np.all(a['restrictions'] == empty, axis=1))
            cls.states, cls.restrictions = a['states'][ids], a['restrictions'][ids]
        with contextlib.redirect_stdout(io.StringIO()):
            cls.patterns, _, cls.inherited = assemble(cls.data)
            cls.extras = extra_blocks(cls.data, cls.states)

    def test_ordered_marked_products_and_exact_certificate(self):
        self.assertEqual(len(self.extras), 1)
        self.assertEqual(self.extras[0]['flags'], list(range(10)))
        v = np.arange(1, 11, dtype=float)
        value = float(block_score(self.extras[0], np.outer(v, v))[0])
        marks = list(combinations(range(5), 3))
        total = 0
        for roots in combinations(range(7), 3):
            rest = tuple(i for i in range(7) if i not in roots)
            for left in combinations(rest, 2):
                right = tuple(i for i in rest if i not in left)
                a, b = tuple(sorted(roots+left)), tuple(sorted(roots+right))
                ma = marks.index(tuple(a.index(i) for i in roots))
                mb = marks.index(tuple(b.index(i) for i in roots))
                total += (ma+1)*(mb+1)
        self.assertAlmostEqual(value, total/210, places=12)
        factors = [np.zeros((len(b['flags']), 0)) for b in self.inherited]
        factors += [np.zeros((64, 0)), v[:, None]]
        bound, cert = certify_expanded(self.patterns, self.inherited, factors,
            self.extras, self.states, self.restrictions, 16)
        self.assertEqual(bound, Q(total, 210))
        cert.update(summands=2, coefficient=self.data['coefficient'], tuples=self.data['tuples'])
        self.assertEqual(Q(verify(self.data, self.states, self.restrictions, cert)['exact_bound']), bound)
        from verify_primal_sdp7 import validate_full_flag_basis
        with self.assertRaises(ValueError):
            validate_full_flag_basis(self.data, cert)
        bad = json.loads(json.dumps(cert))
        bad['extra_blocks'][0]['factor'][0][0] += 10**10
        with self.assertRaises(ValueError):
            verify(self.data, self.states, self.restrictions, bad)
        bad = json.loads(json.dumps(cert))
        bad['extra_blocks'][0]['denominator'] = 0
        with self.assertRaises(ValueError):
            verify(self.data, self.states, self.restrictions, bad)

    def test_sparse_products_match_saved_exact_negative_forms(self):
        diagnostic = json.loads((self.base/'c4_missing_blocks_diagnostic.json').read_text())
        primal = json.loads((self.base/'sdp7_c4_global_primal_repair/primal_certificate.json').read_text())
        with np.load(self.base/'sdp7_c4_global/cover7.npz') as a:
            states = a['states'][primal['indices']]
        weights = np.array(primal['weight_numerators'], dtype=float)
        weights /= weights.sum()
        with contextlib.redirect_stdout(io.StringIO()):
            blocks = extra_blocks(self.data, states)
        for block, saved in zip(blocks, diagnostic['blocks']):
            vector = dict(zip(saved['flag_codes'], saved['vector_integers']))
            v = np.array([vector.get(flag, 0)/saved['vector_denominator'] for flag in block['flags']])
            computed = float(block_score(block, np.outer(v, v)) @ weights)
            self.assertAlmostEqual(computed, float(Q(saved['quadratic_exact'])), places=13)

    def test_factor_gradient(self):
        from refine_expanded_sdp7 import ExpandedObjective
        from sdp7 import sparse
        rng = np.random.default_rng(735)

        def block(n, columns):
            pairs = [(i, j) for j in range(n) for i in range(j+1)]
            return dict(flags=list(range(n)), pairs=pairs,
                        operator=sparse.csc_matrix(rng.normal(size=(len(pairs), columns))))

        inherited, root, extra = block(2, 3), block(2, 4), block(3, 4)
        restrictions = rng.integers(0, 3, size=(4, 7))
        function = ExpandedObjective(np.array([.4, .5, .6]), [inherited], root,
                                     [extra], restrictions, .01, [2])
        x = rng.normal(size=int(function.offsets[-1]))*.1
        _, gradient = function(x)
        for i in range(len(x)):
            step = np.zeros_like(x); step[i] = 1e-6
            derivative = (function(x+step)[0]-function(x-step)[0])/2e-6
            self.assertAlmostEqual(gradient[i], derivative, places=7)

    def test_five_root_normalization_and_verifier(self):
        with contextlib.redirect_stdout(io.StringIO()):
            extras = extra_blocks(self.data, self.states, five_roots='all')
        self.assertEqual([(b['t'], b['f']) for b in extras], [(3, 5), (5, 6)])
        marks = list(combinations(range(6), 5))
        total = 0
        for roots in combinations(range(7), 5):
            rest = tuple(i for i in range(7) if i not in roots)
            for v in rest:
                a = tuple(sorted(roots+(v,)))
                b = tuple(sorted(roots+tuple(i for i in rest if i != v)))
                ma = marks.index(tuple(a.index(i) for i in roots))
                mb = marks.index(tuple(b.index(i) for i in roots))
                total += (ma+1)*(mb+1)
        factors = [np.zeros((len(b['flags']), 0)) for b in self.inherited]
        factors += [np.zeros((64, 0)), np.zeros((10, 0)), np.arange(1, 7, dtype=float)[:, None]]
        bound, cert = certify_expanded(self.patterns, self.inherited, factors,
            extras, self.states, self.restrictions, 16)
        self.assertEqual(bound, Q(total, 42))
        cert.update(summands=2, coefficient=self.data['coefficient'], tuples=self.data['tuples'])
        self.assertEqual(Q(verify(self.data, self.states, self.restrictions, cert)['exact_bound']), bound)


if __name__ == '__main__':
    unittest.main()
