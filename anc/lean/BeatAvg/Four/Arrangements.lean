import BeatAvg.Four.Families
import BeatAvg.Four.FlagPermutation

namespace BeatAvg.Four
open Fast.Four Function Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem evalK_sum (xs : List Fast.K) : evalK (ksum xs) = (xs.map evalK).sum :=
  BeatAvg.evalK_ksum xs

theorem fn4_injective_lists {l l' : List (Fin 4)} (h : l.length = 4) (h' : l'.length = 4)
    (he : fn4 l = fn4 l') : l = l' := by
  apply List.ext_getElem (by rw [h,h'])
  intro i h1 h2
  have hh := congrFun he ⟨i, by omega⟩
  simpa [fn4, List.getD, h1, h2] using hh

theorem all4_nodup : all4.Nodup := by decide +kernel
theorem all4_good : ∀ l ∈ all4, l.length = 4 ∧ Injective (fn4 l) := by decide +kernel
theorem reps2_nodup : reps2.Nodup := by decide +kernel
theorem reps2_good : ∀ l ∈ reps2, l.length = 4 ∧ Injective (fn4 l) ∧
    Injective (fn4 l ∘ Fast.appendF (pairFamily Data.block0).eR (pairFamily Data.block0).eT) ∧
    Injective (fn4 l ∘ Fast.appendF (pairFamily Data.block0).eR (pairFamily Data.block0).eT') ∧
    StrictMono (fn4 l ∘ (pairFamily Data.block0).eR) ∧
    StrictMono (fn4 l ∘ (pairFamily Data.block0).eT) ∧
    StrictMono (fn4 l ∘ (pairFamily Data.block0).eT') := by decide +kernel

theorem sum_perm_all4 (F : (Fin 4 → Fin 4) → ℝ) :
    (∑ π : Equiv.Perm (Fin 4), F π) = (all4.map fun l => F (fn4 l)).sum := by
  have hh := sum_perm_reps (emb0n 4) (emb0n 4) (emb0n 4)
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) F
    (fun π σ => by rw [ext_empty]) (fun π σ => by rw [ext_empty]) (fun π σ => by rw [ext_empty])
    fn4 all4 all4_nodup
    (fun l hl l' hl' he => fn4_injective_lists (all4_good l hl).1 (all4_good l' hl').1 he)
    (fun l hl => ⟨(all4_good l hl).2, (by intro i; exact i.elim0),
      (by intro i; exact i.elim0), (by intro i; exact i.elim0)⟩) (by decide +kernel)
  simpa using hh

theorem pair_sum_perm (b : Block) {v : Fin 4 → ℝ} (hv : Monotone v) :
    (∑ π : Equiv.Perm (Fin 4), (pairFamily b).term (v ∘ π)) =
      2 * (reps2.map fun l =>
        evalK (expandedEntry b
          (pairFlag b (restrictConfig (configOf v) (fn4 l ∘ sel23)) % (b.flags.size+1))
          (pairFlag b (restrictConfig (configOf v) (fn4 l ∘ sel23')) % (b.flags.size+1)))).sum := by
  have hh := (pairFamily b).sum_perm (pair_injective b) fn4 reps2 reps2_nodup
    (fun l hl l' hl' he => fn4_injective_lists (reps2_good l hl).1 (reps2_good l' hl').1 he)
    (fun l hl => (reps2_good l hl).2) (by decide +kernel) hv
  convert hh using 1
  congr 2
  apply List.map_congr_left
  intro l _
  congr 3
  all_goals apply congrArg (pairFlag b)
  all_goals apply congrArg (restrictConfig (configOf v))
  all_goals funext i; fin_cases i <;> rfl

theorem square_eval (b : Block) (hs : blockShape b = true)
    (he : (List.range b.flags.size).all (expandedRow b) = true)
    {v : Fin 4 → ℝ} (hv : Monotone v) :
    (1/24 : ℝ)*(∑ π : Equiv.Perm (Fin 4), (pairFamily b).term (v ∘ π)) =
      evalK (squareCode b (configOf v)) := by
  rw [pair_sum_perm b hv]
  simp only [squareCode, evalK_smul, evalK_sum, List.map_map, Function.comp_def,
    stored_eq_expanded hs he]
  norm_num
  ring

end BeatAvg.Four
