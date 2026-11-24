import BeatAvg.Five.Matrix
import Fast.Four.Checked

/-! Reuse the existing matrix soundness proofs without altering the old route. -/
namespace BeatAvg.Four
open Fast.Four

theorem enclosure_real : EnclQ Data.low Data.high := by
  have h := enclosure_sound Checked.enclosure
  constructor
  · simpa only [Data.low, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
      using h.lo_nonneg
  · simpa only [Data.low, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
      using h.lo_le
  · simpa only [Data.high, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
      using h.le_hi

theorem block_psd (b : Block) (hs : blockShape b = true)
    (hp : (List.range b.matrix.size).all (psdRow Data.low Data.high b) = true)
    {M : ℕ} (v : Fin M → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * evalK (expandedEntry b i.val j.val) * v j := by
  have hshape : Fast.Five.blockShape (matrixView b) = true := by
    simp only [blockShape, Bool.and_eq_true] at hs
    exact hs.2
  exact BeatAvg.Five.block_psd enclosure_real (matrixView b) hshape hp v

theorem stored_eq_expanded {b : Block} (hs : blockShape b = true)
    (he : (List.range b.flags.size).all (expandedRow b) = true) (i j : ℕ) :
    entryAt b.expanded i j = expandedEntry b i j := by
  have hshape : Fast.Five.blockShape (matrixView b) = true := by
    simp only [blockShape, Bool.and_eq_true] at hs
    exact hs.2
  exact BeatAvg.Five.stored_eq_expanded (b := matrixView b) hshape he i j

theorem endpoint_sound {p : Pattern} (hp : Data.endpointOk p = true) :
    evalK (score Data.blocks p) ≤ Bstar := by
  have hb := BeatAvg.Five.lower_le enclosure_real
    (Fast.K.bstar.sub (score Data.blocks p))
  have hb0 : (0 : ℝ) ≤
      (lower Data.low Data.high (Fast.K.bstar.sub (score Data.blocks p)) : ℝ) := by
    exact_mod_cast (of_decide_eq_true hp : 0 ≤
      lower Data.low Data.high (Fast.K.bstar.sub (score Data.blocks p)))
  rw [evalK_sub, evalK_bstar] at hb
  linarith

end BeatAvg.Four
