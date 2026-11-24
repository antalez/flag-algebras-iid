import BeatAvg.Cert.KSign
import Fast.Psd

/-!
# Soundness of the positive-semidefiniteness check for `Y`
-/

open Finset

namespace BeatAvg

theorem sum_map_range (n : ℕ) (f : ℕ → ℝ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem lin_ub (c a b r : ℝ) (ha : a ≤ r) (hb : r ≤ b) :
    c * r ≤ (if 0 ≤ c then c * b else c * a) := by
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left hb h
  · exact mul_le_mul_of_nonpos_left ha (not_le.mp h).le

theorem cast_ite_lin (q l h : ℚ) :
    (((if 0 ≤ q then q * l else q * h : ℚ)) : ℝ) = if (0 : ℝ) ≤ (q : ℝ) then (q : ℝ) * l else q * h := by
  by_cases hq : 0 ≤ q
  · have : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    simp [hq, this]
  · have : ¬ (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    simp [hq, this]

/-- Real bounds of an enclosure, as rationals. -/
structure EnclQ (l h : ℚ) : Prop where
  l_nonneg : (0 : ℝ) ≤ (l : ℝ)
  l_le : (l : ℝ) ≤ rr
  le_h : rr ≤ (h : ℝ)

theorem enclQ_of {c : Fast.Cert8} (he : Encl c.encLo c.encHi c.encM) :
    EnclQ (Fast.encL c) (Fast.encH c) := by
  obtain ⟨h0, h1, h2⟩ := he
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Fast.encL, Fast.encH] <;> push_cast <;> assumption

theorem lowerQ_le {l h : ℚ} (he : EnclQ l h) (x : Fast.K) :
    ((Fast.K.lowerQ l h x : ℚ) : ℝ) ≤ evalK x := by
  obtain ⟨a0, ha, hb⟩ := he
  have hr0 : 0 ≤ rr := a0.trans ha
  have ha2 : (l : ℝ) * l ≤ rr ^ 2 := by nlinarith
  have hb2 : rr ^ 2 ≤ (h : ℝ) * h := by nlinarith
  have ha3 : (l : ℝ) * l * l ≤ rr ^ 3 := by nlinarith [mul_nonneg a0 a0]
  have hb3 : rr ^ 3 ≤ (h : ℝ) * h * h := by nlinarith [mul_nonneg hr0 hr0]
  have t1 := lin_lb x.b _ _ rr ha hb
  have t2 := lin_lb x.c _ _ (rr ^ 2) ha2 hb2
  have t3 := lin_lb x.d _ _ (rr ^ 3) ha3 hb3
  unfold Fast.K.lowerQ evalK
  push_cast [cast_ite_lin]
  linarith

theorem le_upperQ {l h : ℚ} (he : EnclQ l h) (x : Fast.K) :
    evalK x ≤ ((Fast.K.upperQ l h x : ℚ) : ℝ) := by
  obtain ⟨a0, ha, hb⟩ := he
  have hr0 : 0 ≤ rr := a0.trans ha
  have ha2 : (l : ℝ) * l ≤ rr ^ 2 := by nlinarith
  have hb2 : rr ^ 2 ≤ (h : ℝ) * h := by nlinarith
  have ha3 : (l : ℝ) * l * l ≤ rr ^ 3 := by nlinarith [mul_nonneg a0 a0]
  have hb3 : rr ^ 3 ≤ (h : ℝ) * h * h := by nlinarith [mul_nonneg hr0 hr0]
  have t1 := lin_ub x.b _ _ rr ha hb
  have t2 := lin_ub x.c _ _ (rr ^ 2) ha2 hb2
  have t3 := lin_ub x.d _ _ (rr ^ 3) ha3 hb3
  unfold Fast.K.upperQ evalK
  push_cast [cast_ite_lin]
  linarith

theorem abs_le_absUp {l h : ℚ} (he : EnclQ l h) (x : Fast.K) :
    |evalK x| ≤ ((Fast.K.absUp l h x : ℚ) : ℝ) := by
  have h1 := lowerQ_le he x
  have h2 := le_upperQ he x
  unfold Fast.K.absUp
  rw [abs_le]
  push_cast
  constructor
  · have := le_max_left (-((Fast.K.lowerQ l h x : ℚ) : ℝ)) ((Fast.K.upperQ l h x : ℚ) : ℝ)
    linarith
  · exact h2.trans (le_max_right _ _)

end BeatAvg
