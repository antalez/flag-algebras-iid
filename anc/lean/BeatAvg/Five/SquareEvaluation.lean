import BeatAvg.Five.Arrangements
import BeatAvg.Five.Functional
import BeatAvg.Five.Matrix

namespace BeatAvg.Five
open Fast.Five Function Finset

theorem evalK_sum (xs : List Fast.K) : evalK (ksum xs) = (xs.map evalK).sum :=
  BeatAvg.evalK_ksum xs

theorem square1_eval (b : Block) (hs : blockShape b = true)
    (he : (List.range b.flags.size).all (expandedRow b) = true)
    {v : Fin 5 → ℝ} (hv : Monotone v) :
    (1/120 : ℝ)*(∑ π : Equiv.Perm (Fin 5), (singletonFamily b).term (v ∘ π)) =
      evalK (square1Code b (configOf v)) := by
  rw [singleton_sum_perm b hv]
  simp only [square1Code, evalK_smul, evalK_sum, List.map_map, Function.comp_def,
    stored_eq_expanded hs he]
  norm_num
  ring

theorem square3_eval (b : Block) (hs : blockShape b = true)
    (he : (List.range b.flags.size).all (expandedRow b) = true)
    {v : Fin 5 → ℝ} (hv : Monotone v) :
    (1/120 : ℝ)*(∑ π : Equiv.Perm (Fin 5), (tripleFamily b).term (v ∘ π)) =
      evalK (square3Code b (configOf v)) := by
  rw [triple_sum_perm b hv]
  simp only [square3Code, evalK_smul, evalK_sum, List.map_map, Function.comp_def,
    stored_eq_expanded hs he]
  norm_num
  ring

theorem squares_eval {v : Fin 5 → ℝ} (hv : Monotone v) :
    (1/120 : ℝ)*(∑ π : Equiv.Perm (Fin 5), squares (v ∘ π)) =
      evalK (square1Code Data.block0 (configOf v)) +
      evalK (square3Code Data.block1 (configOf v)) +
      evalK (square3Code Data.block2 (configOf v)) +
      evalK (square3Code Data.block3 (configOf v)) +
      evalK (square3Code Data.block4 (configOf v)) +
      evalK (square3Code Data.block5 (configOf v)) := by
  simp only [squares]
  rw [sum_comm, mul_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change _ = _
  have h0 := square1_eval Data.block0 Checked.shape0 Checked.expanded0 hv
  have h1 := square3_eval Data.block1 Checked.shape1 Checked.expanded1 hv
  have h2 := square3_eval Data.block2 Checked.shape2 Checked.expanded2 hv
  have h3 := square3_eval Data.block3 Checked.shape3 Checked.expanded3 hv
  have h4 := square3_eval Data.block4 Checked.shape4 Checked.expanded4 hv
  have h5 := square3_eval Data.block5 Checked.shape5 Checked.expanded5 hv
  change (1/120)*(∑ π : Equiv.Perm (Fin 5), (singletonFamily Data.block0).term (v ∘ π)) +
    ((1/120)*(∑ π : Equiv.Perm (Fin 5), (tripleFamily Data.block1).term (v ∘ π)) +
    ((1/120)*(∑ π : Equiv.Perm (Fin 5), (tripleFamily Data.block2).term (v ∘ π)) +
    ((1/120)*(∑ π : Equiv.Perm (Fin 5), (tripleFamily Data.block3).term (v ∘ π)) +
    ((1/120)*(∑ π : Equiv.Perm (Fin 5), (tripleFamily Data.block4).term (v ∘ π)) +
    ((1/120)*(∑ π : Equiv.Perm (Fin 5), (tripleFamily Data.block5).term (v ∘ π)) + 0))))) = _
  rw [h0,h1,h2,h3,h4,h5]
  ring

end BeatAvg.Five
