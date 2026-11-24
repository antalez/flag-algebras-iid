import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Block Gram matrices are positive semidefinite
-/

open Finset

namespace BeatAvg

theorem gram_fin {ι κ : Type*} [Fintype ι] (P : Finset κ) (G : κ → ι → ℝ) (u : ι → ℝ) :
    ∑ i, ∑ j, u i * (∑ p ∈ P, G p i * G p j) * u j = ∑ p ∈ P, (∑ i, u i * G p i) ^ 2 := by
  have key : ∀ p, (∑ i, u i * G p i) ^ 2 = ∑ i, ∑ j, u i * (G p i * G p j) * u j := by
    intro p
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    ring
  calc ∑ i, ∑ j, u i * (∑ p ∈ P, G p i * G p j) * u j
      = ∑ i, ∑ j, ∑ p ∈ P, u i * (G p i * G p j) * u j := by
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [mul_sum, sum_mul]
    _ = ∑ i, ∑ p ∈ P, ∑ j, u i * (G p i * G p j) * u j := sum_congr rfl fun i _ => sum_comm
    _ = ∑ p ∈ P, ∑ i, ∑ j, u i * (G p i * G p j) * u j := sum_comm
    _ = ∑ p ∈ P, (∑ i, u i * G p i) ^ 2 := sum_congr rfl fun p _ => (key p).symm

/-- A matrix that is a Gram matrix inside each block and zero across blocks. -/
theorem gram_block_psd (N NB LEN : ℕ) (b : ℕ → ℕ) (r : ℕ → ℕ → ℝ) (hb : ∀ i < N, b i < NB)
    (u : Fin N → ℝ) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N,
      u i * (if b i.val = b j.val then ∑ c ∈ range LEN, r i.val c * r j.val c else 0) * u j := by
  have key : ∀ i j : Fin N,
      (if b i.val = b j.val then ∑ c ∈ range LEN, r i.val c * r j.val c else 0)
      = ∑ p ∈ range NB ×ˢ range LEN,
        (if b i.val = p.1 then r i.val p.2 else 0) * (if b j.val = p.1 then r j.val p.2 else 0) := by
    intro i j
    rw [sum_product]
    have e := sum_eq_single (s := range NB) (b i.val)
      (f := fun β => ∑ c ∈ range LEN,
        (if b i.val = β then r i.val c else 0) * (if b j.val = β then r j.val c else 0))
      (by
        intro β _ hβ
        have : ¬ b i.val = β := fun e => hβ e.symm
        simp [this])
      (by
        intro h
        exact absurd (mem_range.2 (hb i.val i.isLt)) h)
    rw [e]
    by_cases h : b i.val = b j.val
    · simp [h]
    · have h' : ¬ b j.val = b i.val := fun e => h e.symm
      simp [h, h']
  simp only [key]
  rw [gram_fin]
  exact sum_nonneg fun p _ => sq_nonneg _

end BeatAvg
