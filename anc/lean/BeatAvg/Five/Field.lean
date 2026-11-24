import BeatAvg.Cert.PsdSound
import Fast.Five.Checks.Base

/-! Interpret the five-point interval checks as inequalities in the real field. -/
namespace BeatAvg.Five
open Fast.Five

theorem lower_eq (lo hi : ℚ) (x : Fast.K) : lower lo hi x = Fast.K.lowerQ lo hi x := by
  simp only [lower, Fast.K.lowerQ, mul_ite]

theorem upper_eq (lo hi : ℚ) (x : Fast.K) : upper lo hi x = Fast.K.upperQ lo hi x := by
  simp only [upper, Fast.K.upperQ, mul_ite]

theorem lower_le {lo hi : ℚ} (he : EnclQ lo hi) (x : Fast.K) :
    (lower lo hi x : ℝ) ≤ evalK x := by
  rw [lower_eq]
  exact lowerQ_le he x

theorem le_upper {lo hi : ℚ} (he : EnclQ lo hi) (x : Fast.K) :
    evalK x ≤ (upper lo hi x : ℝ) := by
  rw [upper_eq]
  exact le_upperQ he x

theorem abs_le_bound {lo hi : ℚ} (he : EnclQ lo hi) (x : Fast.K) :
    |evalK x| ≤ (absBound lo hi x : ℝ) := by
  simpa only [absBound, lower_eq, upper_eq, Fast.K.absUp] using abs_le_absUp he x

theorem enclosure_real : EnclQ Data.low Data.high := by
  have h := enclosure_sound Checked.enclosure
  constructor
  · simpa only [Data.low, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
      using h.lo_nonneg
  · simpa only [Data.low, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
      using h.lo_le
  · simpa only [Data.high, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
      using h.le_hi

theorem keq_sound {x y : Fast.K} (h : keq x y = true) : x = y := by
  cases x; cases y
  simpa only [keq, Bool.and_eq_true, beq_iff_eq, Fast.K.mk.injEq, and_assoc] using h

/-- The recorded expanded matrix is exactly W Y Wᵀ in Q(r). -/
theorem expanded_entry_sound {b : Block} {i j : ℕ}
    (h : expandedRow b i = true) (hj : j < b.flags.size) :
    entryAt b.expanded i j = expandedEntry b i j := by
  apply keq_sound
  exact (List.all_eq_true.mp h) j (List.mem_range.mpr hj)

/-- A successful endpoint check gives both endpoint inequalities over the reals. -/
theorem endpoint_sound {p : Pattern} (hp : Data.endpointOk p = true) :
    evalK (score Data.blocks Data.wHalf Data.wTwice Data.nu p Fast.K.bstar) ≤ Bstar ∧
    evalK (score Data.blocks Data.wHalf Data.wTwice Data.nu p Fast.K.one) ≤ 1 - 9/10000 := by
  simp only [Data.endpointOk, Bool.and_eq_true, decide_eq_true_eq] at hp
  have hb := lower_le enclosure_real
    (Fast.K.bstar.sub (score Data.blocks Data.wHalf Data.wTwice Data.nu p Fast.K.bstar))
  have h1 := lower_le enclosure_real
    ((Fast.K.ofRat (1-9/10000)).sub (score Data.blocks Data.wHalf Data.wTwice Data.nu p Fast.K.one))
  have hb0 : (0 : ℝ) ≤ (lower Data.low Data.high
      (Fast.K.bstar.sub (score Data.blocks Data.wHalf Data.wTwice Data.nu p Fast.K.bstar)) : ℝ) :=
    by exact_mod_cast hp.1
  have h10 : (0 : ℝ) ≤ (lower Data.low Data.high
      ((Fast.K.ofRat (1-9/10000)).sub (score Data.blocks Data.wHalf Data.wTwice Data.nu p Fast.K.one)) : ℝ) :=
    by exact_mod_cast hp.2
  rw [evalK_sub, evalK_bstar] at hb
  rw [evalK_sub, evalK_ofRat] at h1
  norm_num at h1
  constructor <;> linarith

end BeatAvg.Five
