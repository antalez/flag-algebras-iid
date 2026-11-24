import BeatAvg.Cert.Abel
import BeatAvg.Cert.Combos
import BeatAvg.Cert.PsdSound

/-!
# A valid certificate of non-realizability contradicts realizability
-/

open Finset

namespace BeatAvg

/-- Nonpositive suffix sums against a sorted nonnegative sample give a nonpositive combination. -/
theorem dot_nonpos {n : ℕ} {w : ℕ → ℝ} (hw : SG n w) (c : ℕ → ℤ)
    (h : Fast.sufOk ((List.range n).map c) = true) :
    ((List.range n).map fun j => (c j : ℝ) * w j).sum ≤ 0 := by
  have hz : List.zipWith (fun (a : ℤ) (x : ℝ) => (a : ℝ) * x) ((List.range n).map c)
      ((List.range n).map w) = (List.range n).map fun j => (c j : ℝ) * w j := by
    simp [List.zipWith_map]
  have hchain : ((List.range n).map w).IsChain (· ≤ ·) := by
    apply List.Pairwise.isChain
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
    intro i j _ hj hij
    exact (hw.mono i j hij (List.mem_range.1 hj)).le
  have hhead : ∀ x ∈ ((List.range n).map w).head?, 0 ≤ x := by
    intro x hx
    cases n with
    | zero => simp at hx
    | succ m =>
      rw [List.range_succ_eq_map] at hx
      simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hx
      rw [← hx]; exact hw.nonneg
  have h1 := abel ((List.range n).map c) ((List.range n).map w) (by simp) h hchain hhead
  rw [hz] at h1
  have h2 : ((((List.range n).map c).sum : ℤ) : ℝ) ≤ 0 := by
    exact_mod_cast sufOk_sum_le _ h
  have h3 : 0 ≤ ((List.range n).map w).headD 0 := by
    cases n with
    | zero => simp
    | succ m =>
      rw [List.range_succ_eq_map]
      simpa using hw.nonneg
  have := mul_nonpos_of_nonpos_of_nonneg h2 h3
  linarith

/-- Exchanging the sum over certificate entries and the sum over points. -/
theorem swap_sum (n : ℕ) (w : ℕ → ℝ) (cert : Fast.Cert) (g : ℕ × ℕ × ℕ → ℕ → ℤ) :
    ((List.range n).map fun j => (((cert.map fun e => g e j).sum : ℤ) : ℝ) * w j).sum
      = (cert.map fun e => ((List.range n).map fun j => (g e j : ℝ) * w j).sum).sum := by
  induction cert with
  | nil => simp
  | cons e t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih, ← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    push_cast
    ring

theorem sum_single (n : ℕ) (w : ℕ → ℝ) {t : ℕ} (ht : t < n) (v : ℝ) :
    ∑ j ∈ range n, (if j = t then v else 0) * w j = v * w t := by
  rw [sum_congr rfl fun j _ => ite_mul (j = t) v 0 (w j)]
  simp only [zero_mul]
  rw [sum_ite_eq' (range n) t (fun j => v * w j), if_pos (mem_range.2 ht)]

/-- The linear form of an inequality, evaluated on a sample. -/
theorem coefE_sum (n : ℕ) (w : ℕ → ℝ) (kind : ℕ) {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ Fast.combos n) :
    ((List.range n).map fun j => (Fast.coefE kind q j : ℝ) * w j).sum
      = if kind = 0 then 2 * w q.2.2.2 - w q.1 - w q.2.1 - w q.2.2.1
        else 2 * w q.2.2.1 - w q.1 - w q.2.1 - w q.2.2.2 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_combos.1 hq
  rw [sum_map_range]
  have hc : ∀ j, (Fast.coefE kind q j : ℝ) * w j
      = (if j = (if kind = 0 then q.2.2.2 else q.2.2.1) then (2 : ℝ) else 0) * w j
        - (if j = q.1 then (1 : ℝ) else 0) * w j - (if j = q.2.1 then (1 : ℝ) else 0) * w j
        - (if j = (if kind = 0 then q.2.2.1 else q.2.2.2) then (1 : ℝ) else 0) * w j := by
    intro j
    simp only [Fast.coefE]
    push_cast
    ring
  simp only [hc, sum_sub_distrib]
  by_cases hk : kind = 0
  · simp only [hk, if_true]
    rw [sum_single n w h4, sum_single n w (by omega), sum_single n w (by omega),
      sum_single n w (by omega)]
    ring
  · simp only [hk, if_false]
    rw [sum_single n w (by omega), sum_single n w (by omega), sum_single n w (by omega),
      sum_single n w h4]
    ring

end BeatAvg

namespace BeatAvg

open Finset

theorem list_sum_pos {α : Type*} (l : List α) (f : α → ℝ) (hne : l ≠ []) (hpos : ∀ e ∈ l, 0 < f e) :
    0 < (l.map f).sum := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons]
    have ha := hpos a List.mem_cons_self
    by_cases ht : t = []
    · subst ht; simpa using ha
    · have := ih ht fun e he => hpos e (List.mem_cons_of_mem _ he)
      linarith

/-- Each inequality asserted by the pattern of a sorted sample holds strictly. -/
theorem entry_pos {n : ℕ} {w : ℕ → ℝ} (hw : SG n w) {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ Fast.combos n)
    {kind : ℕ} (hk : kind < 2) :
    0 < (Fast.signOf kind (trit w q) : ℝ) *
      (if kind = 0 then 2 * w q.2.2.2 - w q.1 - w q.2.1 - w q.2.2.1
        else 2 * w q.2.2.1 - w q.1 - w q.2.1 - w q.2.2.2) := by
  obtain ⟨a, b, c, d⟩ := q
  obtain ⟨h1, h2, h3, h4⟩ := mem_combos.1 hq
  simp only at h1 h2 h3 h4 ⊢
  have hcd : w c < w d := hw.mono c d h3 h4
  have hk' : kind = 0 ∨ kind = 1 := by omega
  rcases hk' with rfl | rfl
  · simp only [Fast.signOf, if_true]
    by_cases ht : 1 ≤ trit w (a, b, c, d)
    · have := (trit_ge_one_iff hcd).1 ht
      simp only [ht, if_true]
      push_cast
      linarith
    · have hn : ¬ (w a + w b + w c < 2 * w d) := fun h => ht ((trit_ge_one_iff hcd).2 h)
      have htie := hw.noTie a b c d (by omega) (by omega) (by omega) h4 (by omega) (by omega)
        (by omega)
      have hgt : 2 * w d < w a + w b + w c := lt_of_le_of_ne (not_lt.mp hn) (Ne.symm htie)
      simp only [ht, if_false]
      push_cast
      linarith
  · simp only [Fast.signOf, one_ne_zero, if_false]
    by_cases ht : trit w (a, b, c, d) = 2
    · have := (trit_eq_two_iff hcd).1 ht
      simp only [ht, if_true]
      push_cast
      linarith
    · have hn : ¬ (w a + w b + w d < 2 * w c) := fun h => ht ((trit_eq_two_iff hcd).2 h)
      have htie := hw.noTie a b d c (by omega) (by omega) h4 (by omega) (by omega) (by omega)
        (by omega)
      have hgt : 2 * w c < w a + w b + w d := lt_of_le_of_ne (not_lt.mp hn) (Ne.symm htie)
      simp only [ht, if_false]
      push_cast
      linarith

/-- A valid certificate of non-realizability cannot be attached to the pattern of a sample. -/
theorem farkas_sound {n : ℕ} {w : ℕ → ℝ} (hw : SG n w) (cert : Fast.Cert)
    (h : Fast.farkasOk (Fast.combos n) n (patArr n w) cert = true) : False := by
  simp only [Fast.farkasOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨hne, hall⟩, hsuf⟩ := h
  have hle := dot_nonpos hw (Fast.coefs (Fast.combos n) (patArr n w) cert) hsuf
  have hswap := swap_sum n w cert (fun e j => (e.2.2 : ℤ) *
    Fast.signOf e.2.1 ((patArr n w).getD e.1 0) *
      Fast.coefE e.2.1 ((Fast.combos n).getD e.1 (0, 0, 0, 0)) j)
  have hcoefs : ∀ j, Fast.coefs (Fast.combos n) (patArr n w) cert j
      = (cert.map fun e => (e.2.2 : ℤ) * Fast.signOf e.2.1 ((patArr n w).getD e.1 0) *
        Fast.coefE e.2.1 ((Fast.combos n).getD e.1 (0, 0, 0, 0)) j).sum := fun j => rfl
  simp only [hcoefs] at hle
  rw [hswap] at hle
  have hpos : 0 < (cert.map fun e => ((List.range n).map fun j =>
      (((e.2.2 : ℤ) * Fast.signOf e.2.1 ((patArr n w).getD e.1 0) *
        Fast.coefE e.2.1 ((Fast.combos n).getD e.1 (0, 0, 0, 0)) j : ℤ) : ℝ) * w j).sum).sum := by
    refine list_sum_pos cert _ (by intro hc; simp [hc] at hne) fun e he => ?_
    obtain ⟨⟨hwt, hidx⟩, hkind⟩ := hall e he
    have hq := combos_getD hidx
    have hinner : ((List.range n).map fun j =>
        (((e.2.2 : ℤ) * Fast.signOf e.2.1 ((patArr n w).getD e.1 0) *
          Fast.coefE e.2.1 ((Fast.combos n).getD e.1 (0, 0, 0, 0)) j : ℤ) : ℝ) * w j).sum
        = (e.2.2 : ℝ) * ((Fast.signOf e.2.1 ((patArr n w).getD e.1 0) : ℝ) *
          ((List.range n).map fun j =>
            (Fast.coefE e.2.1 ((Fast.combos n).getD e.1 (0, 0, 0, 0)) j : ℝ) * w j).sum) := by
      rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      push_cast
      ring
    rw [hinner, coefE_sum n w e.2.1 hq, patArr_getD n w hidx]
    exact mul_pos (by exact_mod_cast hwt) (entry_pos hw hq hkind)
  linarith

end BeatAvg
