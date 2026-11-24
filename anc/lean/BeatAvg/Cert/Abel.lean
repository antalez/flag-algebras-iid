import Fast.Farkas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Summation by parts: nonpositive suffix sums against a nondecreasing nonnegative sequence
-/

namespace BeatAvg

theorem sufOk_sum_le (l : List ℤ) (h : Fast.sufOk l = true) : l.sum ≤ 0 := by
  cases l with
  | nil => simp
  | cons a t =>
    simp only [Fast.sufOk, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa using h.2

theorem abel (as : List ℤ) : ∀ (ws : List ℝ), as.length = ws.length → Fast.sufOk as = true →
    ws.IsChain (· ≤ ·) → (∀ w ∈ ws.head?, 0 ≤ w) →
    (List.zipWith (fun (a : ℤ) (w : ℝ) => (a : ℝ) * w) as ws).sum
      ≤ ((as.sum : ℤ) : ℝ) * ws.headD 0 := by
  induction as with
  | nil =>
    intro ws hlen _ _ _
    cases ws with
    | nil => simp
    | cons w ws' => simp at hlen
  | cons a t ih =>
    intro ws hlen hsuf hchain hhead
    cases ws with
    | nil => simp at hlen
    | cons w ws' =>
      simp only [Fast.sufOk, Bool.and_eq_true, decide_eq_true_eq] at hsuf
      have hw : 0 ≤ w := hhead w (by simp)
      have hlen' : t.length = ws'.length := by simpa using hlen
      have hts : ((t.sum : ℤ) : ℝ) ≤ 0 := by exact_mod_cast sufOk_sum_le t hsuf.1
      simp only [List.zipWith_cons_cons, List.sum_cons, List.headD_cons]
      cases ws' with
      | nil =>
        have ht : t = [] := List.length_eq_zero_iff.1 (by simpa using hlen')
        subst ht
        simp
      | cons w' ws'' =>
        have hww' : w ≤ w' := by
          have := hchain
          simp only [List.isChain_cons_cons] at this
          exact this.1
        have hchain' : (w' :: ws'').IsChain (· ≤ ·) := by
          have := hchain
          simp only [List.isChain_cons_cons] at this
          exact this.2
        have h1 := ih (w' :: ws'') hlen' hsuf.1 hchain' (fun x hx => by
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
          rw [← hx]; exact hw.trans hww')
        simp only [List.headD_cons] at h1
        have h2 : ((t.sum : ℤ) : ℝ) * w' ≤ ((t.sum : ℤ) : ℝ) * w :=
          mul_le_mul_of_nonpos_left hww' hts
        rw [Int.cast_add]
        linarith

end BeatAvg
