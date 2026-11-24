"""Regression checks for the seven-point moment normalization."""
import unittest
import contextlib
import io
import json
from pathlib import Path

import numpy as np

from sdp7 import root_block, root_scores, assemble, exact_certificate, fit7, unpack, sparse, minimax_blend
from verify_sdp7 import verify
from refine_sdp7 import FactorObjective
from verify_primal_sdp7 import positive_semidefinite_bareiss,verify_primal
from optimal_sdp7 import IncrementalLP,FeasibilityLP
from repair_primal_sdp7 import project_weights,RepairObjective
from scs_sdp7 import scs_pairing,fit_scs,fit_scs_dual


class SevenPointTests(unittest.TestCase):
    def test_scs_triangle_permutation_and_feasible_warm_start(self):
        states=np.zeros((1,35),dtype=np.uint8)
        block=root_block(states,1)
        pairs,permutation=scs_pairing(block)
        q=np.arange(16,dtype=float).reshape(4,4)
        q=q+q.T
        packed=np.array([q[i,j]*(1 if i==j else np.sqrt(2)) for i,j in pairs])
        np.testing.assert_allclose(block['operator'][permutation,:].T @ packed,
                                   root_scores(states,q,1))
        try:
            import scs
        except ImportError:
            self.skipTest('Optional SCS unavailable')
        info,_,weights=fit_scs(np.array([0.]),[block],[np.zeros((4,4))],np.array([1.]),0.,10,1e-8)
        self.assertEqual(info['status'],'solved')
        np.testing.assert_allclose(weights,[1.],atol=1e-7)
        info,_,weights=fit_scs_dual(np.array([0.]),[block],[np.zeros((4,4))],
                                     np.array([1.]),0.,10,1e-8)
        self.assertEqual(info['status'],'solved')
        np.testing.assert_allclose(weights,[1.],atol=1e-7)

    def test_convex_primal_repair_projection_and_gradient(self):
        np.testing.assert_allclose(project_weights(np.zeros(2),np.array([0.,1.]),.75),[.25,.75],atol=1e-12)
        rng=np.random.default_rng(127)
        block=dict(flags=[0,1],pairs=[(0,0),(0,1),(1,1)],
                   operator=sparse.csc_matrix(rng.normal(size=(3,4))))
        function=RepairObjective([block],1e-5)
        weights=np.array([.1,.2,.3,.4])
        _,gradient,_=function(weights)
        for i in range(4):
            step=np.zeros(4);step[i]=1e-6
            derivative=(function(weights+step)[0]-function(weights-step)[0])/(2e-6)
            self.assertAlmostEqual(gradient[i],derivative,places=6)

    def test_exact_primal_psd_test_detects_hidden_indefiniteness(self):
        gram=np.array([[1,2],[3,4],[5,6]],dtype=object)
        self.assertEqual(positive_semidefinite_bareiss((gram @ gram.T).tolist()),2)
        self.assertEqual(positive_semidefinite_bareiss([[0,0],[0,3]]),1)
        for matrix in ([[0,1],[1,0]],[[1,2],[2,1]],
                       [[10**18,10**18+1],[10**18+1,10**18+2]]):
            with self.assertRaises(ValueError):
                positive_semidefinite_bareiss(matrix)

    def test_incremental_lp_cuts_and_feasibility_margin(self):
        try:
            import highspy
        except ImportError:
            self.skipTest('Optional highspy unavailable')
        objective=np.array([.4,.6])
        rows=[sparse.csr_matrix([[1.,-1.]])]
        lp=IncrementalLP(objective,10)
        result=lp.solve(rows,np.zeros(1))
        self.assertTrue(result.success)
        self.assertAlmostEqual(float(objective @ result.x),.5)
        rows.append(sparse.csr_matrix([[1.,-2.]]))
        result=lp.solve(rows,np.zeros(2))
        self.assertTrue(result.success)
        self.assertAlmostEqual(float(objective @ result.x),.4*2/3+.6/3)
        feasibility=FeasibilityLP(objective,10,.49)
        result=feasibility.solve(rows[:1],[1.],.49)
        self.assertTrue(result.success)
        self.assertAlmostEqual(result.gamma,.1)
        self.assertAlmostEqual(result.objective_multiplier,10.)

    def test_independent_exact_primal_for_constant_law(self):
        here=Path(__file__).resolve().parent
        archive_path=here/'results/sdp7_c0/cover7.npz'
        certificate_path=here/'results/sdp7_c0_factor_refinement/certificate.json'
        if not archive_path.exists() or not certificate_path.exists():
            self.skipTest('Saved seven-point artifacts unavailable')
        data=json.loads((here/'results/sdp6_c0/c152137_100000/cover.json').read_text())
        upper=json.loads(certificate_path.read_text())
        index6=data['patterns'].index('-'*len(data['tuples']))
        with np.load(archive_path) as archive:
            states,restrictions=archive['states'],archive['restrictions']
        index7=int(np.flatnonzero(np.all(restrictions==index6,axis=1))[0])
        checked=verify_primal(data,states,restrictions,upper,[index7],[1])
        self.assertTrue(checked['exact_psd'])
        self.assertEqual(checked['exact_lower'],'0')
        self.assertEqual(checked['blocks'][-1]['rank'],4)
        incomplete=json.loads(json.dumps(upper))
        incomplete['inherited']['blocks'].pop()
        with self.assertRaisesRegex(ValueError,'full inherited flag basis'):
            verify_primal(data,states,restrictions,incomplete,[index7],[1])

    def test_unrestricted_factor_gradient_against_finite_differences(self):
        rng=np.random.default_rng(178)
        pairs=[(0,0),(0,1),(1,1)]
        block=dict(flags=[0,1],pairs=pairs,operator=sparse.csc_matrix(rng.normal(size=(3,4))))
        root=dict(flags=[0,1],pairs=pairs,operator=sparse.csc_matrix(rng.normal(size=(3,5))))
        restrictions=rng.integers(0,4,size=(5,7))
        objective=FactorObjective(rng.normal(size=4),[block],root,restrictions,.2)
        x=rng.normal(size=8)*.2
        _,gradient=objective(x)
        for i in range(len(x)):
            step=np.zeros_like(x)
            step[i]=1e-6
            difference=(objective(x+step)[0]-objective(x-step)[0])/(2e-6)
            self.assertAlmostEqual(gradient[i],difference,places=6)

    def test_minimax_blend_checks_the_full_cover(self):
        a, b = np.array([1., .8]), np.array([.9, 1.2])
        alpha = minimax_blend(a,b)
        self.assertAlmostEqual(alpha,.4)
        self.assertAlmostEqual(float(np.max((1-alpha)*a+alpha*b)),.96)
        self.assertEqual(minimax_blend(a,a+1),0.)
        self.assertEqual(minimax_blend(a,a-1),1.)

    def test_ordered_pair_normalization_and_exact_pairing(self):
        states = np.random.default_rng(73).integers(0, 16, size=(30, 35), dtype=np.uint8)
        block = root_block(states, 16)
        multiplicities = np.array([1 if i == j else 2 for i, j in block['pairs']])
        np.testing.assert_array_equal(block['counts'].T @ multiplicities, np.full(30, 140))
        factor = np.arange(64 * 3, dtype=np.int64).reshape(64, 3) - 23
        gram = factor @ factor.T
        coeff = np.array([gram[i, j] * (1 if i == j else 2) for i, j in block['pairs']])
        exact = root_scores(states, gram, 16)
        np.testing.assert_array_equal(block['counts'].T @ coeff, exact)
        floating = root_scores(states, gram.astype(float), 16)
        np.testing.assert_allclose(floating, np.asarray(exact, dtype=float) / 140)
        svec = np.array([gram[i, j] * (1 if i == j else np.sqrt(2)) for i, j in block['pairs']])
        np.testing.assert_allclose(block['operator'].T @ svec, floating)
        np.testing.assert_allclose(root_scores(states, np.ones((64, 64)), 16), 1)

    def test_big_integer_scores_do_not_overflow(self):
        states = np.zeros((1, 35), dtype=np.uint8)
        gram = np.full((4, 4), 10**30, dtype=object)
        self.assertEqual(root_scores(states, gram, 1)[0], 140 * 10**30)

    def test_constant_law_is_psd_and_solver_feasible(self):
        # If all sampled values lie close to 1, no event succeeds for c<2.
        # Its single seven-point pattern must be a feasible primal law.
        states = np.zeros((1, 35), dtype=np.uint8)
        block = root_block(states, 1)
        moment = unpack(block['operator'].toarray()[:, 0], block['pairs'], 4)
        self.assertGreaterEqual(np.linalg.eigvalsh(moment)[0], -1e-14)
        info, _, weights = fit7(np.array([0.]), [block], np.array([0]), 10, 1e-8)
        self.assertEqual(info['status'], 'Solved')
        self.assertLess(info['primal_residual'], 1e-7)
        np.testing.assert_allclose(weights, [1.], atol=1e-7)
        info, _, _ = fit7(np.array([0.]), [block], np.array([0]), 10, 1e-8, chordal=True)
        self.assertEqual(info['status'], 'Solved')

    def test_moment_slack_is_diagonal_and_accounts_for_trace(self):
        block = dict(flags=[0], pairs=[(0,0)], operator=sparse.csc_matrix([[-.01]]))
        info, _, weights = fit7(np.array([.3]), [block], np.array([0]), 10, 1e-8,
                                moment_slack=.02)
        self.assertEqual(info['status'], 'Solved')
        np.testing.assert_allclose(weights, [1.], atol=1e-7)

    def test_independent_evaluator_with_nonzero_root_and_inherited_factors(self):
        here = Path(__file__).resolve().parent
        archive_path = here/'results/sdp7_c0/cover7.npz'
        if not archive_path.exists():
            self.skipTest('Saved seven-point archive unavailable')
        data = json.loads((here/'results/sdp6_c0/c152137_100000/cover.json').read_text())
        with np.load(archive_path) as archive:
            selected = np.random.default_rng(12).choice(len(archive['states']), 8, replace=False)
            states, restrictions = archive['states'][selected], archive['restrictions'][selected]
        with contextlib.redirect_stdout(io.StringIO()):
            patterns, _, blocks = assemble(data, ((3, 4),))
        rng = np.random.default_rng(101)
        factors = [rng.integers(-3, 4, size=(len(b['flags']), 2)) for b in blocks]
        factors.append(rng.integers(-3, 4, size=(64, 2)))
        matrices = [factor @ factor.T for factor in factors]
        bound, certificate = exact_certificate(patterns, blocks, matrices, states, restrictions, 16)
        certificate.update(summands=2, coefficient=data['coefficient'], tuples=data['tuples'])
        result = verify(data, states, restrictions, certificate)
        self.assertEqual(result['exact_bound'], str(bound))
        certificate['exact_bound'] = str(bound+1)
        with self.assertRaisesRegex(ValueError, 'Claimed bound'):
            verify(data, states, restrictions, certificate)


if __name__ == '__main__':
    unittest.main()
