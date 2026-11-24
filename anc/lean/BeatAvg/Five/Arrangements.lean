import BeatAvg.Five.Families
import BeatAvg.Five.FlagPermutation
import Fast.Five.Arrangements

namespace BeatAvg.Five
open Fast.Five Function Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem fn5_injective_lists {l l' : List (Fin 5)} (h : l.length = 5) (h' : l'.length = 5)
    (he : fn5 l = fn5 l') : l = l' := by
  apply List.ext_getElem (by rw [h,h'])
  intro i h1 h2
  have hh := congrFun he ⟨i, by omega⟩
  simpa [fn5, List.getD, h1, h2] using hh

theorem all5_nodup : all5.Nodup := by decide +kernel

theorem all5_good : ∀ l ∈ all5, l.length = 5 ∧ Injective (fn5 l) := by decide +kernel

theorem reps1_nodup : reps1.Nodup := by decide +kernel
theorem reps3_nodup : reps3.Nodup := by decide +kernel

theorem reps1_good : ∀ l ∈ reps1, l.length = 5 ∧ Injective (fn5 l) ∧
    Injective (fn5 l ∘ Fast.appendF (singletonFamily Data.block0).eR (singletonFamily Data.block0).eT) ∧
    Injective (fn5 l ∘ Fast.appendF (singletonFamily Data.block0).eR (singletonFamily Data.block0).eT') ∧
    StrictMono (fn5 l ∘ (singletonFamily Data.block0).eR) ∧
    StrictMono (fn5 l ∘ (singletonFamily Data.block0).eT) ∧
    StrictMono (fn5 l ∘ (singletonFamily Data.block0).eT') := by decide +kernel

theorem reps3_good : ∀ l ∈ reps3, l.length = 5 ∧ Injective (fn5 l) ∧
    Injective (fn5 l ∘ Fast.appendF (tripleFamily Data.block1).eR (tripleFamily Data.block1).eT) ∧
    Injective (fn5 l ∘ Fast.appendF (tripleFamily Data.block1).eR (tripleFamily Data.block1).eT') ∧
    StrictMono (fn5 l ∘ (tripleFamily Data.block1).eR) ∧
    StrictMono (fn5 l ∘ (tripleFamily Data.block1).eT) ∧
    StrictMono (fn5 l ∘ (tripleFamily Data.block1).eT') := by decide +kernel

theorem sum_perm_all5 (F : (Fin 5 → Fin 5) → ℝ) :
    (∑ π : Equiv.Perm (Fin 5), F π) = (all5.map fun l => F (fn5 l)).sum := by
  have hh := sum_perm_reps (emb0n 5) (emb0n 5) (emb0n 5)
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) F
    (fun π σ => by rw [ext_empty]) (fun π σ => by rw [ext_empty]) (fun π σ => by rw [ext_empty])
    fn5 all5 all5_nodup
    (fun l hl l' hl' he => fn5_injective_lists (all5_good l hl).1 (all5_good l' hl').1 he)
    (fun l hl => ⟨(all5_good l hl).2, (by intro i; exact i.elim0),
      (by intro i; exact i.elim0), (by intro i; exact i.elim0)⟩) (by decide +kernel)
  simpa using hh

theorem singleton_sum_perm (b : Block) {v : Fin 5 → ℝ} (hv : Monotone v) :
    (∑ π : Equiv.Perm (Fin 5), (singletonFamily b).term (v ∘ π)) =
      4 * (reps1.map fun l =>
        evalK (expandedEntry b
          (singletonFlag b (restrictConfig (configOf v) (fn5 l ∘ sel13)) % (b.flags.size+1))
          (singletonFlag b (restrictConfig (configOf v) (fn5 l ∘ sel13')) % (b.flags.size+1)))).sum := by
  have hh := (singletonFamily b).sum_perm (singleton_injective b) fn5 reps1 reps1_nodup
    (fun l hl l' hl' he => fn5_injective_lists (reps1_good l hl).1 (reps1_good l' hl').1 he)
    (fun l hl => (reps1_good l hl).2) (by decide +kernel) hv
  convert hh using 1
  congr 2
  apply List.map_congr_left
  intro l _
  congr 3
  all_goals apply congrArg (singletonFlag b)
  all_goals apply congrArg (restrictConfig (configOf v))
  all_goals funext i; fin_cases i <;> rfl

theorem triple_sum_perm (b : Block) {v : Fin 5 → ℝ} (hv : Monotone v) :
    (∑ π : Equiv.Perm (Fin 5), (tripleFamily b).term (v ∘ π)) =
      6 * (reps3.map fun l =>
        evalK (expandedEntry b
          (tripleFlag b (restrictConfig (configOf v) (fn5 l ∘ sel34)) % (b.flags.size+1))
          (tripleFlag b (restrictConfig (configOf v) (fn5 l ∘ sel34')) % (b.flags.size+1)))).sum := by
  have hh := (tripleFamily b).sum_perm (triple_injective b) fn5 reps3 reps3_nodup
    (fun l hl l' hl' he => fn5_injective_lists (reps3_good l hl).1 (reps3_good l' hl').1 he)
    (fun l hl => (reps3_good l hl).2) (by decide +kernel) hv
  convert hh using 1
  congr 2
  apply List.map_congr_left
  intro l _
  congr 3
  all_goals apply congrArg (tripleFlag b)
  all_goals apply congrArg (restrictConfig (configOf v))
  all_goals funext i; fin_cases i <;> rfl

end BeatAvg.Five
