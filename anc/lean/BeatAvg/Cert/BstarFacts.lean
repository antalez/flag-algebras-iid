import BeatAvg.Cert.KReal

/-!
# Facts about `r` and `B*`
-/

open Set

namespace BeatAvg

/-- `r` is the only root of `x^4 - 4x^3 - 3x^2 - 2x + 2` in `[0, 1]`. -/
theorem rr_unique {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (h : fpoly x = 0) : x = rr := by
  have hr := rr_mem
  rcases lt_trichotomy x rr with hlt | heq | hgt
  · have := fpoly_strictAnti hx.1 hlt hr.2
    rw [h, rr_root] at this
    exact absurd this (lt_irrefl _)
  · exact heq
  · have := fpoly_strictAnti hr.1 hgt hx.2
    rw [h, rr_root] at this
    exact absurd this (lt_irrefl _)

/-- `B* = r (2 - r) / (1 + r + r^2 + r^3)`, the value of the Bellec–Fritz lower bound at `p = r`. -/
theorem Bstar_eq : Bstar = rr * (2 - rr) / (1 + rr + rr ^ 2 + rr ^ 3) := by
  have hr := rr_mem
  have hpos : 0 < 1 + rr + rr ^ 2 + rr ^ 3 := by
    have := hr.1
    positivity
  have hroot : rr ^ 4 - 4 * rr ^ 3 - 3 * rr ^ 2 - 2 * rr + 2 = 0 := by
    have := rr_root; unfold fpoly at this; exact this
  unfold Bstar
  rw [eq_div_iff hpos.ne']
  linear_combination ((rr ^ 2 - rr) / 4) * hroot

end BeatAvg

namespace BeatAvg

open Set

theorem rr_bounds : (47434645 : ℝ) / 100000000 < rr ∧ rr < 47434646 / 100000000 := by
  have hr := rr_mem
  constructor
  · by_contra hc
    have hle : rr ≤ 47434645 / 100000000 := not_lt.mp hc
    have hpos : 0 < fpoly (47434645 / 100000000) := by unfold fpoly; norm_num
    rcases hle.lt_or_eq with hlt | heq
    · have := fpoly_strictAnti hr.1 hlt (by norm_num)
      rw [rr_root] at this
      linarith
    · rw [← heq, rr_root] at hpos
      exact absurd hpos (lt_irrefl _)
  · by_contra hc
    have hle : (47434646 : ℝ) / 100000000 ≤ rr := not_lt.mp hc
    have hneg : fpoly (47434646 / 100000000) < 0 := by unfold fpoly; norm_num
    rcases hle.lt_or_eq with hlt | heq
    · have := fpoly_strictAnti (by norm_num) hlt hr.2
      rw [rr_root] at this
      linarith
    · rw [heq, rr_root] at hneg
      exact absurd hneg (lt_irrefl _)

/-- `B* = 0.40069537...`. -/
theorem Bstar_bounds : (40069537 : ℝ) / 100000000 < Bstar ∧ Bstar < 40069538 / 100000000 := by
  obtain ⟨h1, h2⟩ := rr_bounds
  -- `g(x) = x^3 - 6x^2 + 6x` is increasing on `[0.47, 0.48]`
  have hmono : ∀ x y : ℝ, (47 : ℝ) / 100 ≤ x → x < y → y ≤ 48 / 100 →
      x ^ 3 - 6 * x ^ 2 + 6 * x < y ^ 3 - 6 * y ^ 2 + 6 * y := by
    intro x y hx hxy hy
    have h : y ^ 3 - 6 * y ^ 2 + 6 * y - (x ^ 3 - 6 * x ^ 2 + 6 * x)
        = (y - x) * (y ^ 2 + y * x + x ^ 2 - 6 * (y + x) + 6) := by ring
    have hb : 0 < y ^ 2 + y * x + x ^ 2 - 6 * (y + x) + 6 := by nlinarith
    have := mul_pos (sub_pos.2 hxy) hb
    linarith
  have ha := hmono (47434645 / 100000000) rr (by norm_num) h1 (by linarith)
  have hb := hmono rr (47434646 / 100000000) (by linarith) h2 (by norm_num)
  unfold Bstar
  constructor
  · have : (40069537 : ℝ) / 100000000 * 4
        < (47434645 / 100000000 : ℝ) ^ 3 - 6 * (47434645 / 100000000) ^ 2
          + 6 * (47434645 / 100000000) := by norm_num
    linarith
  · have : (47434646 / 100000000 : ℝ) ^ 3 - 6 * (47434646 / 100000000) ^ 2
          + 6 * (47434646 / 100000000) < (40069538 : ℝ) / 100000000 * 4 := by norm_num
    linarith

end BeatAvg
