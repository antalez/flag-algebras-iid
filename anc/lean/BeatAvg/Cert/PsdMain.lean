import BeatAvg.Cert.PsdSound
import Mathlib.Data.List.GetD

/-!
# `Y` is positive semidefinite
-/

open Finset

namespace BeatAvg

/-- A matrix that dominates its off-diagonal entries row by row is positive semidefinite. -/
theorem quad_nonneg_of_diag_dom (n : ℕ) (R : ℕ → ℕ → ℝ) (u : ℕ → ℝ)
    (hdom : ∀ a ∈ range n, ∑ b ∈ range n, (if b = a then 0 else (|R a b| + |R b a|) / 2) ≤ R a a) :
    0 ≤ ∑ a ∈ range n, ∑ b ∈ range n, u a * R a b * u b := by
  -- off-diagonal weights
  let m : ℕ → ℕ → ℝ := fun a b => if b = a then 0 else |R a b|
  have hterm : ∀ a ∈ range n, ∀ b ∈ range n,
      (if b = a then R a a * u a ^ 2 else 0) - m a b * u a ^ 2 / 2 - m a b * u b ^ 2 / 2
        ≤ u a * R a b * u b := by
    intro a _ b _
    by_cases h : b = a
    · subst h; simp only [m, if_true]; ring_nf; exact le_refl _
    · simp only [m, h, if_false]
      have h1 : -(|R a b| * |u a * u b|) ≤ R a b * (u a * u b) := by
        have := neg_abs_le (R a b * (u a * u b))
        rwa [abs_mul] at this
      have h2 : |u a * u b| ≤ (u a ^ 2 + u b ^ 2) / 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u a + u b), sq_nonneg (u a - u b)]
      have h3 := mul_le_mul_of_nonneg_left h2 (abs_nonneg (R a b))
      nlinarith
  have hsum : ∑ a ∈ range n, ∑ b ∈ range n,
      ((if b = a then R a a * u a ^ 2 else 0) - m a b * u a ^ 2 / 2 - m a b * u b ^ 2 / 2)
        ≤ ∑ a ∈ range n, ∑ b ∈ range n, u a * R a b * u b :=
    sum_le_sum fun a ha => sum_le_sum fun b hb => hterm a ha b hb
  refine le_trans ?_ hsum
  -- rewrite the lower bound as a sum of nonnegative terms
  have e1 : ∑ a ∈ range n, ∑ b ∈ range n, (if b = a then R a a * u a ^ 2 else 0)
      = ∑ a ∈ range n, R a a * u a ^ 2 := by
    refine sum_congr rfl fun a ha => ?_
    rw [sum_ite_eq' (range n) a (fun _ => R a a * u a ^ 2), if_pos ha]
  have e2 : ∑ a ∈ range n, ∑ b ∈ range n, m a b * u b ^ 2 / 2
      = ∑ a ∈ range n, ∑ b ∈ range n, m b a * u a ^ 2 / 2 := sum_comm
  have e3 : ∑ a ∈ range n, ∑ b ∈ range n,
      ((if b = a then R a a * u a ^ 2 else 0) - m a b * u a ^ 2 / 2 - m a b * u b ^ 2 / 2)
      = ∑ a ∈ range n, (R a a - ∑ b ∈ range n, (m a b + m b a) / 2) * u a ^ 2 := by
    simp only [sum_sub_distrib]
    rw [e1, e2, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [sub_mul, sum_mul]
    have h5 : ∑ i ∈ range n, (m a i + m i a) / 2 * u a ^ 2
        = ∑ x ∈ range n, m a x * u a ^ 2 / 2 + ∑ b ∈ range n, m b a * u a ^ 2 / 2 := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun b _ => by ring
    rw [h5]
    ring
  rw [e3]
  refine sum_nonneg fun a ha => mul_nonneg ?_ (sq_nonneg _)
  have h := hdom a ha
  have e4 : ∑ b ∈ range n, (m a b + m b a) / 2
      = ∑ b ∈ range n, (if b = a then 0 else (|R a b| + |R b a|) / 2) := by
    refine sum_congr rfl fun b _ => ?_
    by_cases hb : b = a
    · subst hb; simp [m]
    · have hb' : ¬ a = b := fun h => hb h.symm
      simp [m, hb, hb']
  rw [e4]
  linarith

end BeatAvg

namespace BeatAvg

open Finset

theorem gram_quad (n : ℕ) (g : ℕ → ℕ → ℝ) (u : ℕ → ℝ) :
    ∑ a ∈ range n, ∑ b ∈ range n, u a * (∑ k ∈ range n, g k a * g k b) * u b
      = ∑ k ∈ range n, (∑ a ∈ range n, u a * g k a) ^ 2 := by
  have key : ∀ k, (∑ a ∈ range n, u a * g k a) ^ 2
      = ∑ a ∈ range n, ∑ b ∈ range n, u a * (g k a * g k b) * u b := by
    intro k
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    ring
  calc ∑ a ∈ range n, ∑ b ∈ range n, u a * (∑ k ∈ range n, g k a * g k b) * u b
      = ∑ a ∈ range n, ∑ b ∈ range n, ∑ k ∈ range n, u a * (g k a * g k b) * u b := by
        refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
        rw [mul_sum, sum_mul]
    _ = ∑ a ∈ range n, ∑ k ∈ range n, ∑ b ∈ range n, u a * (g k a * g k b) * u b :=
        sum_congr rfl fun a _ => sum_comm
    _ = ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, u a * (g k a * g k b) * u b := sum_comm
    _ = ∑ k ∈ range n, (∑ a ∈ range n, u a * g k a) ^ 2 :=
        sum_congr rfl fun k _ => (key k).symm

/-- The structural dot product, as a sum over indices. -/
theorem dotL_cast (ca cb : List ℤ) : ∀ n, ca.length ≤ n →
    ((Fast.dotL ca cb : ℤ) : ℝ) = ∑ k ∈ range n, ((ca.getD k 0 : ℤ) : ℝ) * ((cb.getD k 0 : ℤ) : ℝ) := by
  induction ca generalizing cb with
  | nil =>
    intro n _
    cases cb <;> simp [Fast.dotL]
  | cons x xs ih =>
    intro n hn
    cases cb with
    | nil => simp [Fast.dotL]
    | cons y ys =>
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
      rw [sum_range_succ']
      simp only [Fast.dotL, List.getD_cons_succ, List.getD_cons_zero]
      push_cast
      rw [ih ys m (by simpa using hn)]
      ring

theorem dotL_comm (ca cb : List ℤ) : Fast.dotL ca cb = Fast.dotL cb ca := by
  induction ca generalizing cb with
  | nil => cases cb <;> simp [Fast.dotL]
  | cons x xs ih =>
    cases cb with
    | nil => simp [Fast.dotL]
    | cons y ys => simp only [Fast.dotL, ih ys, mul_comm]

/-- The shape of the certificate matrices. -/
structure Shape (c : Fast.Cert8) : Prop where
  yLen : c.Yr.length = 255
  gLen : c.Gc.length = 255
  yRow : ∀ r ∈ c.Yr, r.length = 255
  gCol : ∀ r ∈ c.Gc, r.length = 255

theorem shape_of {c : Fast.Cert8} (h : Fast.shapeOk c = true) : Shape c := by
  simp only [Fast.shapeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem Shape.col_le {c : Fast.Cert8} (hs : Shape c) (a : ℕ) : (c.Gc.getD a []).length ≤ 255 := by
  by_cases ha : a < c.Gc.length
  · rw [List.getD_eq_getElem _ _ ha, hs.gCol _ (List.getElem_mem ha)]
  · rw [List.getD_eq_default _ _ (by omega)]; simp

theorem gtg_cast (c : Fast.Cert8) (hs : Shape c) (a b : ℕ) :
    ((Fast.gtg c a b : ℤ) : ℝ) = ∑ k ∈ range 255,
      (((c.Gc.getD a []).getD k 0 : ℤ) : ℝ) * (((c.Gc.getD b []).getD k 0 : ℤ) : ℝ) :=
  dotL_cast _ _ 255 (hs.col_le a)

theorem evalK_Rk (c : Fast.Cert8) (hs : Shape c) (a b : ℕ) :
    evalK (Fast.yAt c.Yr a b)
      = evalK (Fast.Rk c a b) + (∑ k ∈ range 255,
        (((c.Gc.getD a []).getD k 0 : ℤ) : ℝ) * (((c.Gc.getD b []).getD k 0 : ℤ) : ℝ))
          / (4 : ℝ) ^ c.gT := by
  unfold Fast.Rk Fast.Rof
  rw [evalK_sub, evalK_ofRat, ← gtg_cast c hs]
  push_cast
  ring

/-- The bounds summed along a row. -/
theorem offSum_eq (l h : ℚ) (a : ℕ) (L : List Fast.K) : ∀ k,
    Fast.offSum l h a k L
      = ∑ j ∈ range L.length, (if k + j = a then 0 else Fast.K.absUp l h (L.getD j Fast.K.zero)) := by
  induction L with
  | nil => intro k; simp [Fast.offSum]
  | cons x xs ih =>
    intro k
    rw [List.length_cons, sum_range_succ', Fast.offSum, ih (k + 1)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [show k + 1 + j = k + (j + 1) by ring]

theorem getD_zipWith {α β γ : Type*} (f : α → β → γ) (l1 : List α) (l2 : List β) (d1 : α) (d2 : β)
    (d : γ) {j : ℕ} (h1 : j < l1.length) (h2 : j < l2.length) :
    (List.zipWith f l1 l2).getD j d = f (l1.getD j d1) (l2.getD j d2) := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h1,
    List.getD_eq_getElem _ _ h2, List.getElem_zipWith]

theorem eqb_eq {x y : Fast.K} (h : Fast.K.eqb x y = true) : x = y := by
  simp only [Fast.K.eqb, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases x; cases y; simp_all

/-- `Y` is symmetric. -/
theorem yAt_symm {c : Fast.Cert8} (h : (List.range 255).all (Fast.symRow c) = true) {a b : ℕ}
    (ha : a < 255) (hb : b < 255) : Fast.yAt c.Yr a b = Fast.yAt c.Yr b a := by
  have key : ∀ a b, a < 255 → b < 255 → a < b → Fast.yAt c.Yr a b = Fast.yAt c.Yr b a := by
    intro a b ha hb hab
    have h1 := List.all_eq_true.1 h a (List.mem_range.2 ha)
    unfold Fast.symRow at h1
    have h2 := List.all_eq_true.1 h1 b (List.mem_range.2 hb)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
    rcases h2 with h2 | h2
    · omega
    · exact eqb_eq h2
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact key a b ha hb hab
  · rfl
  · exact (key b a hb ha hab).symm

theorem Rk_symm {c : Fast.Cert8} (h : (List.range 255).all (Fast.symRow c) = true) {a b : ℕ}
    (ha : a < 255) (hb : b < 255) : Fast.Rk c a b = Fast.Rk c b a := by
  unfold Fast.Rk Fast.gtg
  rw [yAt_symm h ha hb, dotL_comm]

theorem psd_dom (c : Fast.Cert8) (he : Encl c.encLo c.encHi c.encM) (h : Fast.psdOk c = true) :
    ∀ a ∈ range 255, ∑ b ∈ range 255,
      (if b = a then 0 else (|evalK (Fast.Rk c a b)| + |evalK (Fast.Rk c b a)|) / 2)
        ≤ evalK (Fast.Rk c a a) := by
  intro a ha
  have ha' : a < 255 := mem_range.1 ha
  have heQ := enclQ_of he
  simp only [Fast.psdOk, Bool.and_eq_true] at h
  obtain ⟨⟨hshape, hsym⟩, hrows⟩ := h
  have hs := shape_of hshape
  have hrow : Fast.rowOkI c a = true := List.all_eq_true.1 hrows a (List.mem_range.2 ha')
  unfold Fast.rowOkI Fast.rowOk at hrow
  have h1 := of_decide_eq_true hrow
  have hya : (c.Yr.getD a []).length = 255 := by
    rw [List.getD_eq_getElem _ _ (by rw [hs.yLen]; exact ha')]
    exact hs.yRow _ (List.getElem_mem _)
  rw [offSum_eq, List.length_zipWith, hya, hs.gLen, min_self] at h1
  have h2 : ∑ b ∈ range 255, (if b = a then (0 : ℚ) else
      Fast.K.absUp (Fast.encL c) (Fast.encH c) (Fast.Rk c a b))
      ≤ Fast.K.lowerQ (Fast.encL c) (Fast.encH c) (Fast.Rk c a a) := by
    refine le_trans (le_of_eq (sum_congr rfl fun b hb => ?_)) h1
    have hb' : b < 255 := mem_range.1 hb
    rw [zero_add, getD_zipWith _ _ _ Fast.K.zero [] _ (by rw [hya]; exact hb')
      (by rw [hs.gLen]; exact hb')]
    rfl
  have h3 : ((∑ b ∈ range 255, (if b = a then (0 : ℚ) else
      Fast.K.absUp (Fast.encL c) (Fast.encH c) (Fast.Rk c a b)) : ℚ) : ℝ)
      ≤ ((Fast.K.lowerQ (Fast.encL c) (Fast.encH c) (Fast.Rk c a a) : ℚ) : ℝ) := by
    exact_mod_cast h2
  rw [Rat.cast_sum] at h3
  refine le_trans (sum_le_sum fun b hb => ?_) (h3.trans (lowerQ_le heQ _))
  by_cases hba : b = a
  · simp [hba]
  · simp only [hba, ite_false]
    rw [← Rk_symm hsym ha' (mem_range.1 hb)]
    have e1 := abs_le_absUp heQ (Fast.Rk c a b)
    linarith

/-- `Y` is positive semidefinite. -/
theorem Y_psd (c : Fast.Cert8) (he : Encl c.encLo c.encHi c.encM) (h : Fast.psdOk c = true)
    (u : ℕ → ℝ) :
    0 ≤ ∑ a ∈ range 255, ∑ b ∈ range 255, u a * evalK (Fast.yAt c.Yr a b) * u b := by
  have hs : (0 : ℝ) < (4 : ℝ) ^ c.gT := by positivity
  have hsh : Shape c := by
    simp only [Fast.psdOk, Bool.and_eq_true] at h
    exact shape_of h.1.1
  have hR := quad_nonneg_of_diag_dom 255 (fun a b => evalK (Fast.Rk c a b)) u (psd_dom c he h)
  have hG := gram_quad 255 (fun k a => (((c.Gc.getD a []).getD k 0 : ℤ) : ℝ)) u
  have hsplit : ∑ a ∈ range 255, ∑ b ∈ range 255, u a * evalK (Fast.yAt c.Yr a b) * u b
      = ∑ a ∈ range 255, ∑ b ∈ range 255, u a * evalK (Fast.Rk c a b) * u b
        + (∑ a ∈ range 255, ∑ b ∈ range 255, u a * (∑ k ∈ range 255,
          (((c.Gc.getD a []).getD k 0 : ℤ) : ℝ) * (((c.Gc.getD b []).getD k 0 : ℤ) : ℝ)) * u b)
          / (4 : ℝ) ^ c.gT := by
    rw [sum_div, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_div, ← sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [evalK_Rk c hsh]
    ring
  rw [hsplit, hG]
  have : 0 ≤ (∑ k ∈ range 255, (∑ a ∈ range 255, u a * (((c.Gc.getD a []).getD k 0 : ℤ) : ℝ)) ^ 2)
      / (4 : ℝ) ^ c.gT := div_nonneg (sum_nonneg fun k _ => sq_nonneg _) hs.le
  linarith

end BeatAvg
