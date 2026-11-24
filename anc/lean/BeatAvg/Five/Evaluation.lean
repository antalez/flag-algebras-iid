import BeatAvg.Five.ScalarEvaluation
import BeatAvg.Five.SquareEvaluation

namespace BeatAvg.Five
open Fast.Five Function Finset

/-- Exact evaluation of the symmetrized five-point sample functional from the
recorded pattern. All probability and finite-check terms now meet here. -/
theorem Lam_eval {p : Pattern} {v : Fin 5 → ℝ}
    (hv : Generic v) (hm : Monotone v)
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) (x : Fast.K) :
    Lam (evalK x) v = evalK (assembledScore Data.blocks Data.wHalf Data.wTwice Data.nu p x) := by
  have hc := configOf_eq_pattern hv hm hb
  have hsplit : ∀ w, lam (evalK x) w = scalarSample (evalK x) w + squares w := by
    intro w
    unfold lam scalarSample
    ring
  simp only [Lam, hsplit, sum_add_distrib, mul_add]
  rw [squares_eval hm, sum_perm_all5 (fun ρ => scalarSample (evalK x) (v ∘ ρ))]
  have hmap : (all5.map fun l => scalarSample (evalK x) (v ∘ fn5 l)) =
      all5.map fun l => evalK (scalarCode Data.blocks Data.wHalf Data.wTwice Data.nu (configOf v) (fn5 l) x) := by
    exact List.map_congr_left fun l hl => scalarSample_eval hv (all5_good l hl).2 x
  rw [hmap]
  unfold assembledScore
  rw [← hc]
  simp only [evalK_add, evalK_smul, evalK_sum, List.map_map, Function.comp_def]
  norm_num [Data.blocks, List.range_succ]
  ring

/-- The sample functional is invariant under reordering, as in the original proof. -/
theorem Lam_comp_perm (x : ℝ) (v : Fin 5 → ℝ) (σ : Equiv.Perm (Fin 5)) :
    Lam x (v ∘ σ) = Lam x v := by
  unfold Lam
  congr 1
  have hh := Equiv.sum_comp (Equiv.mulLeft σ)
    (fun π : Equiv.Perm (Fin 5) => lam x (v ∘ π))
  rw [← hh]
  rfl

theorem Generic.comp_perm {n : ℕ} {v : Fin n → ℝ} (hv : Generic v) (σ : Equiv.Perm (Fin n)) :
    Generic (v ∘ σ) := by
  refine ⟨fun i => hv.1 _, hv.2.1.comp σ.injective, ?_, ?_⟩
  · intro a b c d had hbd hcd
    exact hv.2.2.1 _ _ _ _ (σ.injective.ne had) (σ.injective.ne hbd) (σ.injective.ne hcd)
  · intro i j hij
    exact hv.2.2.2 _ _ (σ.injective.ne hij)

end BeatAvg.Five
