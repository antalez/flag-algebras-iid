import Fast.K
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The real number `r`, evaluation of `Q(r)` in `ℝ`, and certified signs
-/

namespace BeatAvg

open Set

/-- `f(x) = x^4 - 4x^3 - 3x^2 - 2x + 2`. -/
def fpoly (x : ℝ) : ℝ := x ^ 4 - 4 * x ^ 3 - 3 * x ^ 2 - 2 * x + 2

theorem fpoly_strictAnti {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 1) : fpoly y < fpoly x := by
  have h : fpoly y - fpoly x =
      (y - x) * (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3 - 4 * (y ^ 2 + y * x + x ^ 2)
        - 3 * (y + x) - 2) := by unfold fpoly; ring
  have hy0 : 0 ≤ y := hx.trans hxy.le
  have hx1 : x ≤ 1 := hxy.le.trans hy
  have hneg : y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3 - 4 * (y ^ 2 + y * x + x ^ 2)
      - 3 * (y + x) - 2 < 0 := by
    have h1 : y ^ 3 ≤ y ^ 2 := by nlinarith [sq_nonneg y]
    have h2 : x ^ 3 ≤ x ^ 2 := by nlinarith [sq_nonneg x]
    have h3 : y ^ 2 * x ≤ y * x := by nlinarith [mul_nonneg hy0 hx]
    have h4 : y * x ^ 2 ≤ y * x := by nlinarith [mul_nonneg hy0 hx]
    nlinarith [mul_nonneg hy0 hx, sq_nonneg y, sq_nonneg x]
  have := mul_neg_of_pos_of_neg (sub_pos.2 hxy) hneg
  linarith

theorem exists_root : ∃ x ∈ Icc (0 : ℝ) 1, fpoly x = 0 := by
  have hc : ContinuousOn fpoly (Icc 0 1) := by unfold fpoly; fun_prop
  have h := intermediate_value_Icc' (zero_le_one (α := ℝ)) hc
  have hm : (0 : ℝ) ∈ Icc (fpoly 1) (fpoly 0) := by unfold fpoly; constructor <;> norm_num
  obtain ⟨x, hx, hfx⟩ := h hm
  exact ⟨x, hx, hfx⟩

/-- The root of `x^4 - 4x^3 - 3x^2 - 2x + 2` in `[0, 1]`. -/
noncomputable def rr : ℝ := Classical.choose exists_root

theorem rr_mem : rr ∈ Icc (0 : ℝ) 1 := (Classical.choose_spec exists_root).1

theorem rr_root : fpoly rr = 0 := (Classical.choose_spec exists_root).2

theorem rr_pow4 : rr ^ 4 = 4 * rr ^ 3 + 3 * rr ^ 2 + 2 * rr - 2 := by
  have := rr_root; unfold fpoly at this; linarith

/-- Real value of an element of `Q(r)`. -/
noncomputable def evalK (x : Fast.K) : ℝ := x.a + x.b * rr + x.c * rr ^ 2 + x.d * rr ^ 3

/-- Real value of an element of `Z[r]`. -/
noncomputable def evalZ (x : Fast.Z4) : ℝ := x.a + x.b * rr + x.c * rr ^ 2 + x.d * rr ^ 3

/-- `B* = (r^3 - 6 r^2 + 6 r) / 4`. -/
noncomputable def Bstar : ℝ := (rr ^ 3 - 6 * rr ^ 2 + 6 * rr) / 4

@[simp] theorem evalK_zero : evalK Fast.K.zero = 0 := by simp [evalK, Fast.K.zero]

theorem evalK_ofRat (q : ℚ) : evalK (Fast.K.ofRat q) = q := by simp [evalK, Fast.K.ofRat]

theorem evalK_add (x y : Fast.K) : evalK (x.add y) = evalK x + evalK y := by
  simp only [evalK, Fast.K.add, Rat.cast_add]; ring

theorem evalK_sub (x y : Fast.K) : evalK (x.sub y) = evalK x - evalK y := by
  simp only [evalK, Fast.K.sub, Rat.cast_sub]; ring

theorem evalK_smul (q : ℚ) (x : Fast.K) : evalK (Fast.K.smul q x) = q * evalK x := by
  simp only [evalK, Fast.K.smul, Rat.cast_mul]; ring

theorem evalK_mul (x y : Fast.K) : evalK (x.mul y) = evalK x * evalK y := by
  have h4 := rr_pow4
  have h5 : rr ^ 5 = -8 + 6 * rr + 14 * rr ^ 2 + 19 * rr ^ 3 := by
    have : rr ^ 5 = rr * rr ^ 4 := by ring
    rw [this, h4]; ring_nf; rw [h4]; ring
  have h6 : rr ^ 6 = -38 + 30 * rr + 63 * rr ^ 2 + 90 * rr ^ 3 := by
    have : rr ^ 6 = rr * rr ^ 5 := by ring
    rw [this, h5]; ring_nf; rw [h4]; ring
  simp only [evalK, Fast.K.mul, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
  linear_combination (-(↑x.b * ↑y.d + ↑x.c * ↑y.c + ↑x.d * ↑y.b : ℝ)) * h4
    - (↑x.c * ↑y.d + ↑x.d * ↑y.c : ℝ) * h5 - (↑x.d * ↑y.d : ℝ) * h6

theorem evalK_bstar : evalK Fast.K.bstar = Bstar := by
  simp only [evalK, Fast.K.bstar, Bstar]; push_cast; ring

@[simp] theorem evalZ_zero : evalZ Fast.Z4.zero = 0 := by simp [evalZ, Fast.Z4.zero]

theorem evalZ_add (x y : Fast.Z4) : evalZ (x.add y) = evalZ x + evalZ y := by
  simp only [evalZ, Fast.Z4.add, Int.cast_add]; ring

theorem evalZ_sub (x y : Fast.Z4) : evalZ (x.sub y) = evalZ x - evalZ y := by
  simp only [evalZ, Fast.Z4.sub, Int.cast_sub]; ring

theorem evalZ_smul (n : ℤ) (x : Fast.Z4) : evalZ (Fast.Z4.smul n x) = n * evalZ x := by
  simp only [evalZ, Fast.Z4.smul, Int.cast_mul]; ring

theorem evalZ_mul (x y : Fast.Z4) : evalZ (x.mul y) = evalZ x * evalZ y := by
  have h4 := rr_pow4
  have h5 : rr ^ 5 = -8 + 6 * rr + 14 * rr ^ 2 + 19 * rr ^ 3 := by
    have : rr ^ 5 = rr * rr ^ 4 := by ring
    rw [this, h4]; ring_nf; rw [h4]; ring
  have h6 : rr ^ 6 = -38 + 30 * rr + 63 * rr ^ 2 + 90 * rr ^ 3 := by
    have : rr ^ 6 = rr * rr ^ 5 := by ring
    rw [this, h5]; ring_nf; rw [h4]; ring
  simp only [evalZ, Fast.Z4.mul, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  linear_combination (-(↑x.b * ↑y.d + ↑x.c * ↑y.c + ↑x.d * ↑y.b : ℝ)) * h4
    - (↑x.c * ↑y.d + ↑x.d * ↑y.c : ℝ) * h5 - (↑x.d * ↑y.d : ℝ) * h6

end BeatAvg
