import BeatAvg.Cert.KReal

/-!
# Certified enclosure of `r`, certified nonnegativity in `Z[r]`, clearing denominators
-/

namespace BeatAvg

open Set

theorem fNum_cast (p : ℤ) (m : ℕ) :
    ((Fast.fNum p m : ℤ) : ℝ) = ((2 : ℝ) ^ m) ^ 4 * fpoly ((p : ℝ) / 2 ^ m) := by
  have hE : ((2 : ℝ) ^ m) ≠ 0 := by positivity
  unfold Fast.fNum fpoly
  push_cast
  field_simp

/-- A certified enclosure of `r`. -/
structure Encl (lo hi : ℤ) (m : ℕ) : Prop where
  lo_nonneg : (0 : ℝ) ≤ (lo : ℝ) / 2 ^ m
  lo_le : (lo : ℝ) / 2 ^ m ≤ rr
  le_hi : rr ≤ (hi : ℝ) / 2 ^ m

theorem enclosure_sound {lo hi : ℤ} {m : ℕ} (h : Fast.enclosureOk lo hi m = true) :
    Encl lo hi m := by
  simp only [Fast.enclosureOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h0, hlt⟩, h1⟩, hflo⟩, hfhi⟩ := h
  have hE : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hE4 : (0 : ℝ) < ((2 : ℝ) ^ m) ^ 4 := by positivity
  have hflo' : 0 < fpoly ((lo : ℝ) / 2 ^ m) := by
    have h2 : (0 : ℝ) < ((Fast.fNum lo m : ℤ) : ℝ) := by exact_mod_cast hflo
    rw [fNum_cast] at h2
    by_contra hc
    have := mul_nonpos_of_nonneg_of_nonpos hE4.le (not_lt.mp hc)
    linarith
  have hfhi' : fpoly ((hi : ℝ) / 2 ^ m) < 0 := by
    have h2 : ((Fast.fNum hi m : ℤ) : ℝ) < 0 := by exact_mod_cast hfhi
    rw [fNum_cast] at h2
    by_contra hc
    have := mul_nonneg hE4.le (not_lt.mp hc)
    linarith
  have hlo0 : (0 : ℝ) ≤ (lo : ℝ) / 2 ^ m := div_nonneg (by exact_mod_cast h0) hE.le
  have hhi1 : (hi : ℝ) / 2 ^ m ≤ 1 := (div_le_one hE).2 (by exact_mod_cast h1)
  have hlohi : (lo : ℝ) / 2 ^ m < (hi : ℝ) / 2 ^ m :=
    div_lt_div_of_pos_right (by exact_mod_cast hlt) hE
  have hr := rr_mem
  refine ⟨hlo0, ?_, ?_⟩
  · by_contra hc
    have := fpoly_strictAnti hr.1 (not_le.mp hc) (hlohi.le.trans hhi1)
    rw [rr_root] at this
    linarith
  · by_contra hc
    have := fpoly_strictAnti (hlo0.trans hlohi.le) (not_le.mp hc) hr.2
    rw [rr_root] at this
    linarith

theorem lin_lb (c a b r : ℝ) (ha : a ≤ r) (hb : r ≤ b) :
    (if 0 ≤ c then c * a else c * b) ≤ c * r := by
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left ha h
  · exact mul_le_mul_of_nonpos_left hb (not_le.mp h).le

theorem lowerNum_cast (lo hi : ℤ) (m : ℕ) (x : Fast.Z4) :
    ((Fast.Z4.lowerNum lo hi m x : ℤ) : ℝ) = ((2 : ℝ) ^ m) ^ 3 * ((x.a : ℝ)
      + (if (0 : ℝ) ≤ x.b then (x.b : ℝ) * ((lo : ℝ) / 2 ^ m) else x.b * ((hi : ℝ) / 2 ^ m))
      + (if (0 : ℝ) ≤ x.c then (x.c : ℝ) * ((lo : ℝ) / 2 ^ m) ^ 2 else x.c * ((hi : ℝ) / 2 ^ m) ^ 2)
      + (if (0 : ℝ) ≤ x.d then (x.d : ℝ) * ((lo : ℝ) / 2 ^ m) ^ 3
          else x.d * ((hi : ℝ) / 2 ^ m) ^ 3)) := by
  have hE : ((2 : ℝ) ^ m) ≠ 0 := by positivity
  unfold Fast.Z4.lowerNum
  by_cases hb : 0 ≤ x.b <;> by_cases hc : 0 ≤ x.c <;> by_cases hd : 0 ≤ x.d <;>
    simp only [hb, hc, hd, Int.cast_nonneg_iff, ite_true, ite_false] <;> push_cast <;> field_simp

theorem nonneg_sound {lo hi : ℤ} {m : ℕ} (he : Encl lo hi m) {x : Fast.Z4}
    (h : Fast.Z4.nonneg lo hi m x = true) : 0 ≤ evalZ x := by
  simp only [Fast.Z4.nonneg, decide_eq_true_eq] at h
  have h1 : (0 : ℝ) ≤ ((Fast.Z4.lowerNum lo hi m x : ℤ) : ℝ) := by exact_mod_cast h
  rw [lowerNum_cast] at h1
  have hE3 : (0 : ℝ) < ((2 : ℝ) ^ m) ^ 3 := by positivity
  have h2 := nonneg_of_mul_nonneg_right h1 hE3
  obtain ⟨a0, ha, hb⟩ := he
  have hr0 : 0 ≤ rr := a0.trans ha
  have ha2 : ((lo : ℝ) / 2 ^ m) ^ 2 ≤ rr ^ 2 := pow_le_pow_left₀ a0 ha 2
  have hb2 : rr ^ 2 ≤ ((hi : ℝ) / 2 ^ m) ^ 2 := pow_le_pow_left₀ hr0 hb 2
  have ha3 : ((lo : ℝ) / 2 ^ m) ^ 3 ≤ rr ^ 3 := pow_le_pow_left₀ a0 ha 3
  have hb3 : rr ^ 3 ≤ ((hi : ℝ) / 2 ^ m) ^ 3 := pow_le_pow_left₀ hr0 hb 3
  have t1 := lin_lb x.b _ _ rr ha hb
  have t2 := lin_lb x.c _ _ (rr ^ 2) ha2 hb2
  have t3 := lin_lb x.d _ _ (rr ^ 3) ha3 hb3
  unfold evalZ
  linarith

theorem toZ4_sound {n : ℤ} {x : Fast.K} (h : Fast.K.integralAt n x = true) :
    evalZ (Fast.K.toZ4 n x) = n * evalK x := by
  simp only [Fast.K.integralAt, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h
  have key : ∀ q : ℚ, (q * n).den = 1 → (((q * n).num : ℤ) : ℝ) = (n : ℝ) * (q : ℝ) := by
    intro q hq
    have h1 : ((q * n : ℚ) : ℝ) = (((q * n).num : ℤ) : ℝ) := by
      conv_lhs => rw [← Rat.num_div_den (q * n), hq]
      simp
    rw [← h1]; push_cast; ring
  simp only [evalZ, evalK, Fast.K.toZ4]
  rw [key _ ha, key _ hb, key _ hc, key _ hd]
  ring

end BeatAvg
