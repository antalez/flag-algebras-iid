import BeatAvg.Four.Arrangements
import BeatAvg.Four.Functional
import BeatAvg.Four.PatternConfig
import Fast.Four.Objective

namespace BeatAvg.Four
open Fast.Four Function Finset
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem wins_lt (p : Pattern) : wins p < 3 := by
  unfold wins
  split_ifs <;> omega

theorem objective_eval (v : Fin 4 → ℝ) {ρ : Fin 4 → Fin 4} (hρ : Injective ρ) :
    ind S4 (v ∘ ρ) =
      (bitNat ((configOf v).additive.sb (ρ 0) (ρ 1) (ρ 2) (ρ 3)) : ℝ) := by
  have hb (b : Bool) : (bitNat b : ℝ) = if b then 1 else 0 := by
    cases b <;> norm_num [bitNat]
  rw [hb]
  exact objG_eval id v hρ

theorem objective_mean {p : Pattern} {v : Fin 4 → ℝ}
    (hc : configOf v = patternConfig p) :
    (1/24 : ℝ)*(∑ π : Equiv.Perm (Fin 4), ind S4 (v ∘ π)) =
      (wins p : ℝ)/4 := by
  rw [sum_perm_all4 (fun ρ => ind S4 (v ∘ ρ))]
  have hm : (all4.map fun l => ind S4 (v ∘ fn4 l)) =
      all4.map fun l =>
        (bitNat ((patternConfig p).additive.sb (fn4 l 0) (fn4 l 1)
          (fn4 l 2) (fn4 l 3)) : ℝ) := by
    apply List.map_congr_left
    intro l hl
    rw [objective_eval v (all4_good l hl).2, hc]
  rw [hm]
  have hh : (all4.map fun l =>
        (bitNat ((patternConfig p).additive.sb (fn4 l 0) (fn4 l 1)
          (fn4 l 2) (fn4 l 3)) : ℝ)).sum = (objectiveCount (wins p) : ℝ) := by
    simp only [objectiveCount, patternConfig, additiveTrits,
      Nat.cast_list_sum, List.map_map, Function.comp_def]
  rw [hh, objectiveCount_ok ⟨wins p, wins_lt p⟩]
  push_cast
  ring

theorem squares_eval {v : Fin 4 → ℝ} (hv : Monotone v) :
    (1/24 : ℝ)*(∑ π : Equiv.Perm (Fin 4), squares (v ∘ π)) =
      evalK (ksum (Data.blocks.toList.map fun b => squareCode b (configOf v))) := by
  simp only [squares]
  rw [sum_comm, mul_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change _ = _
  have h0 := square_eval Data.block0 Checked.shape0 Checked.expanded0 hv
  have h1 := square_eval Data.block1 Checked.shape1 Checked.expanded1 hv
  have h2 := square_eval Data.block2 Checked.shape2 Checked.expanded2 hv
  have h3 := square_eval Data.block3 Checked.shape3 Checked.expanded3 hv
  change (1/24)*(∑ π : Equiv.Perm (Fin 4), (pairFamily Data.block0).term (v ∘ π)) +
    ((1/24)*(∑ π : Equiv.Perm (Fin 4), (pairFamily Data.block1).term (v ∘ π)) +
    ((1/24)*(∑ π : Equiv.Perm (Fin 4), (pairFamily Data.block2).term (v ∘ π)) +
    ((1/24)*(∑ π : Equiv.Perm (Fin 4), (pairFamily Data.block3).term (v ∘ π)) + 0))) = _
  rw [h0,h1,h2,h3]
  norm_num [Data.blocks, evalK_sum, List.map_map, Function.comp_def]

/-- The verified score is the actual symmetrized objective plus flag squares. -/
theorem Lam_eval {p : Pattern} {v : Fin 4 → ℝ}
    (hv : Generic v) (hm : Monotone v)
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    Lam v = evalK (score Data.blocks p) := by
  have hc := configOf_eq_pattern hv hm hb
  simp only [Lam, lam, sum_add_distrib, mul_add]
  rw [objective_mean hc, squares_eval hm, hc]
  simp only [score, evalK_add, evalK_ofRat, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]

end BeatAvg.Four
