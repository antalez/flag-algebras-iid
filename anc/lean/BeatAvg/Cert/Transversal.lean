import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Summing over all orderings a function that is invariant under reordering inside blocks

For a block of positions `b : Fin k ↪ Fin n` and `F` invariant under permutations of the block,
`∑_π F π = k! ∑_{π increasing on the block} F π`.
-/

open Finset Function

namespace BeatAvg

variable {n : ℕ}

/-- Exactly one reordering of an injective tuple is increasing. -/
theorem card_sorting_perm {k : ℕ} {v : Fin k → Fin n} (hv : Injective v) :
    (univ.filter fun σ : Equiv.Perm (Fin k) => StrictMono (v ∘ ⇑σ)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨Tuple.sort v, ?_⟩
  ext σ
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro hσ
    have h1 := Tuple.unique_monotone hσ.monotone (Tuple.monotone_sort v)
    ext i
    have := congrFun h1 i
    simp only [comp_apply] at this
    exact congrArg Fin.val (hv this)
  · rintro rfl
    exact (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)

theorem viaEmbedding_comp {k : ℕ} (b : Fin k ↪ Fin n) (π : Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin k)) : ⇑(π * σ.viaEmbedding b) ∘ ⇑b = ⇑π ∘ ⇑b ∘ ⇑σ := by
  funext i
  simp [Equiv.Perm.viaEmbedding_apply]

/-- One block. -/
theorem sum_perm_block {k : ℕ} (b : Fin k ↪ Fin n) (F : Equiv.Perm (Fin n) → ℝ)
    (hF : ∀ (π : Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin k)), F (π * σ.viaEmbedding b) = F π) :
    ∑ π, F π = (k.factorial : ℝ) * ∑ π : Equiv.Perm (Fin n), if StrictMono (⇑π ∘ ⇑b) then F π else 0 := by
  have h1 : ∀ π : Equiv.Perm (Fin n),
      F π = ∑ σ : Equiv.Perm (Fin k), if StrictMono (⇑π ∘ ⇑b ∘ ⇑σ) then F π else 0 := by
    intro π
    have hc : (univ.filter fun σ : Equiv.Perm (Fin k) => StrictMono (⇑π ∘ ⇑b ∘ ⇑σ)).card = 1 :=
      card_sorting_perm (v := ⇑π ∘ ⇑b) (π.injective.comp b.injective)
    rw [← Finset.sum_filter, Finset.sum_const, hc, one_smul]
  calc ∑ π, F π
      = ∑ π : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin k),
          if StrictMono (⇑π ∘ ⇑b ∘ ⇑σ) then F π else 0 := Finset.sum_congr rfl fun π _ => h1 π
    _ = ∑ σ : Equiv.Perm (Fin k), ∑ π : Equiv.Perm (Fin n),
          if StrictMono (⇑π ∘ ⇑b ∘ ⇑σ) then F π else 0 := Finset.sum_comm
    _ = ∑ σ : Equiv.Perm (Fin k), ∑ π : Equiv.Perm (Fin n),
          if StrictMono (⇑π ∘ ⇑b) then F π else 0 := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        have h2 := Equiv.sum_comp (Equiv.mulRight (σ.viaEmbedding b))
          (fun π : Equiv.Perm (Fin n) => if StrictMono (⇑π ∘ ⇑b) then F π else 0)
        rw [← h2]
        refine Finset.sum_congr rfl fun π _ => ?_
        have e1 : ⇑((Equiv.mulRight (σ.viaEmbedding b)) π) ∘ ⇑b = ⇑π ∘ ⇑b ∘ ⇑σ :=
          viaEmbedding_comp b π σ
        have e2 : F ((Equiv.mulRight (σ.viaEmbedding b)) π) = F π := hF π σ
        rw [e2]
        refine if_congr ?_ rfl rfl
        rw [e1]
    _ = (k.factorial : ℝ) * ∑ π : Equiv.Perm (Fin n), if StrictMono (⇑π ∘ ⇑b) then F π else 0 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- Reordering one block does not move the positions of a disjoint block. -/
theorem viaEmbedding_comp_disjoint {k k' : ℕ} (b : Fin k ↪ Fin n) (b' : Fin k' ↪ Fin n)
    (hd : ∀ i j, b' i ≠ b j) (π : Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin k)) :
    ⇑(π * σ.viaEmbedding b) ∘ ⇑b' = ⇑π ∘ ⇑b' := by
  funext i
  have : b' i ∉ Set.range b := by
    rintro ⟨j, hj⟩
    exact hd i j hj.symm
  simp [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ this]

/-- Three pairwise disjoint blocks. -/
theorem sum_perm_blocks {k1 k2 k3 : ℕ} (b1 : Fin k1 ↪ Fin n) (b2 : Fin k2 ↪ Fin n)
    (b3 : Fin k3 ↪ Fin n) (h12 : ∀ i j, b1 i ≠ b2 j) (h13 : ∀ i j, b1 i ≠ b3 j)
    (h23 : ∀ i j, b2 i ≠ b3 j) (F : Equiv.Perm (Fin n) → ℝ)
    (hF1 : ∀ π σ, F (π * Equiv.Perm.viaEmbedding σ b1) = F π)
    (hF2 : ∀ π σ, F (π * Equiv.Perm.viaEmbedding σ b2) = F π)
    (hF3 : ∀ π σ, F (π * Equiv.Perm.viaEmbedding σ b3) = F π) :
    ∑ π, F π = ((k1.factorial * k2.factorial * k3.factorial : ℕ) : ℝ) *
      ∑ π : Equiv.Perm (Fin n),
        if StrictMono (⇑π ∘ ⇑b1) ∧ StrictMono (⇑π ∘ ⇑b2) ∧ StrictMono (⇑π ∘ ⇑b3) then F π
        else 0 := by
  rw [sum_perm_block b1 F hF1]
  rw [sum_perm_block b2 (fun π => if StrictMono (⇑π ∘ ⇑b1) then F π else 0) (by
    intro π σ
    simp only [viaEmbedding_comp_disjoint b2 b1 h12 π σ, hF2])]
  rw [sum_perm_block b3 (fun π => if StrictMono (⇑π ∘ ⇑b2) then
      (if StrictMono (⇑π ∘ ⇑b1) then F π else 0) else 0) (by
    intro π σ
    simp only [viaEmbedding_comp_disjoint b3 b1 h13 π σ,
      viaEmbedding_comp_disjoint b3 b2 h23 π σ, hF3])]
  push_cast
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  refine Finset.sum_congr rfl fun π _ => ?_
  by_cases c1 : StrictMono (⇑π ∘ ⇑b1) <;> by_cases c2 : StrictMono (⇑π ∘ ⇑b2) <;>
    by_cases c3 : StrictMono (⇑π ∘ ⇑b3) <;> simp [c1, c2, c3]

end BeatAvg

namespace BeatAvg

open Finset Function

variable {n : ℕ}

open Classical in
/-- The permutation of a list whose function is bijective (the identity otherwise). -/
noncomputable def toPerm (fn : List (Fin n) → Fin n → Fin n) (l : List (Fin n)) :
    Equiv.Perm (Fin n) :=
  if h : Bijective (fn l) then Equiv.ofBijective (fn l) h else 1

theorem toPerm_coe (fn : List (Fin n) → Fin n → Fin n) {l : List (Fin n)} (h : Injective (fn l)) :
    ⇑(toPerm fn l) = fn l := by
  have hb : Bijective (fn l) := Finite.injective_iff_bijective.1 h
  unfold toPerm
  rw [dif_pos hb]
  rfl

/-- Sum over all orderings as a sum over a list of representatives: the list has no repetition,
its members are increasing on the three blocks, and it has the right length. -/
theorem sum_perm_reps {k1 k2 k3 : ℕ} (b1 : Fin k1 ↪ Fin n) (b2 : Fin k2 ↪ Fin n)
    (b3 : Fin k3 ↪ Fin n) (h12 : ∀ i j, b1 i ≠ b2 j) (h13 : ∀ i j, b1 i ≠ b3 j)
    (h23 : ∀ i j, b2 i ≠ b3 j) (F : (Fin n → Fin n) → ℝ)
    (hF1 : ∀ (π : Equiv.Perm (Fin n)) σ, F ⇑(π * Equiv.Perm.viaEmbedding σ b1) = F ⇑π)
    (hF2 : ∀ (π : Equiv.Perm (Fin n)) σ, F ⇑(π * Equiv.Perm.viaEmbedding σ b2) = F ⇑π)
    (hF3 : ∀ (π : Equiv.Perm (Fin n)) σ, F ⇑(π * Equiv.Perm.viaEmbedding σ b3) = F ⇑π)
    (fn : List (Fin n) → Fin n → Fin n) (reps : List (List (Fin n))) (hnodup : reps.Nodup)
    (hinj : ∀ l ∈ reps, ∀ l' ∈ reps, fn l = fn l' → l = l')
    (hgood : ∀ l ∈ reps, Injective (fn l) ∧ StrictMono (fn l ∘ ⇑b1) ∧ StrictMono (fn l ∘ ⇑b2) ∧
      StrictMono (fn l ∘ ⇑b3))
    (hcount : reps.length * (k1.factorial * k2.factorial * k3.factorial) = n.factorial) :
    ∑ π : Equiv.Perm (Fin n), F ⇑π
      = ((k1.factorial * k2.factorial * k3.factorial : ℕ) : ℝ) * (reps.map fun l => F (fn l)).sum := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = k1.factorial * k2.factorial * k3.factorial := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  rw [← hK] at hcount ⊢
  obtain ⟨R, hR⟩ : ∃ R : Finset (Equiv.Perm (Fin n)), R = univ.filter fun π : Equiv.Perm (Fin n) =>
      StrictMono (⇑π ∘ ⇑b1) ∧ StrictMono (⇑π ∘ ⇑b2) ∧ StrictMono (⇑π ∘ ⇑b3) := ⟨_, rfl⟩
  -- the block theorem, for `F` and for the constant function
  have hsumF : ∑ π : Equiv.Perm (Fin n), F ⇑π = (K : ℝ) * ∑ π ∈ R, F ⇑π := by
    rw [sum_perm_blocks b1 b2 b3 h12 h13 h23 (fun π => F ⇑π) hF1 hF2 hF3, hR, Finset.sum_filter,
      hK]
  have hsum1 : ((n.factorial : ℕ) : ℝ) = (K : ℝ) * (R.card : ℝ) := by
    have h := sum_perm_blocks b1 b2 b3 h12 h13 h23 (fun _ : Equiv.Perm (Fin n) => (1 : ℝ))
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    rw [← Finset.sum_filter, ← hR, ← hK] at h
    simpa [Fintype.card_perm] using h
  have hcard : R.card = reps.length := by
    have h1 : n.factorial = K * R.card := by exact_mod_cast hsum1
    have h2 : K * R.card = K * reps.length := by rw [← h1, ← hcount, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hKpos h2
  -- the representatives enumerate `R`
  have hmemR : ∀ l ∈ reps, toPerm fn l ∈ R := by
    intro l hl
    obtain ⟨hi, g1, g2, g3⟩ := hgood l hl
    rw [hR, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [toPerm_coe fn hi]
    exact ⟨g1, g2, g3⟩
  have hinjOn : Set.InjOn (toPerm fn) (reps.toFinset : Set (List (Fin n))) := by
    intro l hl l' hl' heq
    have hl1 : l ∈ reps := List.mem_toFinset.1 hl
    have hl2 : l' ∈ reps := List.mem_toFinset.1 hl'
    apply hinj l hl1 l' hl2
    rw [← toPerm_coe fn (hgood l hl1).1, ← toPerm_coe fn (hgood l' hl2).1, heq]
  have hS : reps.toFinset.image (toPerm fn) = R := by
    apply Finset.eq_of_subset_of_card_le
    · intro π hπ
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hπ
      exact hmemR l (List.mem_toFinset.1 hl)
    · rw [Finset.card_image_of_injOn hinjOn, List.toFinset_card_of_nodup hnodup, hcard]
  rw [hsumF, ← hS, Finset.sum_image hinjOn]
  congr 1
  rw [← List.sum_toFinset _ hnodup]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [toPerm_coe fn (hgood l (List.mem_toFinset.1 hl)).1]

theorem ext_mem {n k : ℕ} (b : Fin k ↪ Fin n) (π : Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin k))
    (i : Fin k) : (π * σ.viaEmbedding b) (b i) = π (b (σ i)) := by
  simp [Equiv.Perm.viaEmbedding_apply]

theorem ext_notMem {n k : ℕ} (b : Fin k ↪ Fin n) (π : Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin k))
    {x : Fin n} (hx : ∀ i, x ≠ b i) : (π * σ.viaEmbedding b) x = π x := by
  have : x ∉ Set.range b := by
    rintro ⟨i, hi⟩
    exact hx i hi.symm
  simp [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ this]

theorem ext_empty {n : ℕ} (b : Fin 0 ↪ Fin n) (π : Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin 0)) :
    ⇑(π * σ.viaEmbedding b) = ⇑π :=
  funext fun _ => ext_notMem b π σ fun i => i.elim0

/-- The empty block. -/
def emb0n (n : ℕ) : Fin 0 ↪ Fin n := ⟨fun i => i.elim0, fun i => i.elim0⟩

end BeatAvg
