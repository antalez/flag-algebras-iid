import BeatAvg.K8.Combine
import BeatAvg.K8.Check7K

/-!
# From the level checks to `LevelOk D.G7 40 6`
-/

namespace BeatAvg.K8

theorem lev7T_trans {lo hi : ℕ} (h1 : lev7T lo hi = true) (h2 : lev7D hi = true) (h : lo ≤ hi) :
    lev7D lo = true :=
  all_drop_take _ _ h h1 h2

theorem ordQ3_length : (ordQ 3).length = 0 := by decide
theorem ordQ4_length : (ordQ 4).length = 1 := by decide
theorem ordQ5_length : (ordQ 5).length = 5 := by decide
theorem ordQ6_len : (ordQ 6).length = 15 := by decide
theorem ordQ7_length : (ordQ 7).length = 35 := by decide

theorem ordQ5_len5_3p2 : (ordQ (3 + 2)).length = 5 := by decide
theorem ordQ6_len15 : (ordQ (4 + 2)).length = 15 := by decide
theorem ordQ7_len35 : (ordQ (5 + 2)).length = 35 := by decide
theorem ordQ4_len1 : (ordQ (3 + 1)).length = 1 := by decide
theorem ordQ5_len5 : (ordQ (4 + 1)).length = 5 := by decide
theorem ordQ6_len15' : (ordQ (5 + 1)).length = 15 := by decide

theorem chk5_eq (U : ℕ) : chkLevel D.G4 D.G5 D.X5 2 8 (3 + 1) (ordQ (3 + 2)).length
    (2 * (ordQ (3 + 1)).length) U = chk5 U := by
  rw [ordQ5_len5_3p2, ordQ4_len1]; rfl

theorem chk6_eq (U : ℕ) : chkLevel D.G5 D.G6 D.X6 8 20 (4 + 1) (ordQ (4 + 2)).length
    (2 * (ordQ (4 + 1)).length) U = chk6 U := by
  rw [ordQ6_len15, ordQ5_len5]; rfl

theorem chk7_eq (U : ℕ) : chkLevel D.G6 D.G7 D.X7 20 40 (5 + 1) (ordQ (5 + 2)).length
    (2 * (ordQ (5 + 1)).length) U = chk7 U := by
  rw [ordQ7_len35, ordQ6_len15']; rfl

/-- The levels of five, six and seven points, from the checks. -/
theorem levels (hb : ∀ t, t ≤ 2 → t ∈ unpackE 2 (lookupG D.G4 0).1 (lookupG D.G4 0).2)
    (s3 : statOk 3 = true) (s4 : statOk 4 = true) (s5 : statOk 5 = true)
    (h5 : (allCodes 0 2 D.G4).all chk5 = true) (h6 : (allCodes 2 8 D.G5).all chk6 = true)
    (h7 : lev7D 0 = true) : LevelOk D.G7 40 6 := by
  have l4 : LevelOk D.G4 2 3 := level_base hb
  have l5 : LevelOk D.G5 8 4 := level_step (G := D.G4) (G' := D.G5) (X := D.X5) (wb := 2)
    (wb' := 8) (k := 3) l4 s3 (by
      intro U hU
      rw [ordQ3_length] at hU
      rw [chk5_eq]
      exact List.all_eq_true.1 h5 U hU)
  have l6 : LevelOk D.G6 20 5 := level_step (G := D.G5) (G' := D.G6) (X := D.X6) (wb := 8)
    (wb' := 20) (k := 4) l5 s4 (by
      intro U hU
      rw [ordQ4_length] at hU
      rw [chk6_eq]
      exact List.all_eq_true.1 h6 U hU)
  have h7' : (allCodes 10 20 D.G6).all chk7 = true := by
    unfold lev7D at h7
    rw [List.drop_zero] at h7
    exact h7
  exact level_step (G := D.G6) (G' := D.G7) (X := D.X7) (wb := 20) (wb' := 40) (k := 5) l6 s5 (by
    intro U hU
    rw [ordQ5_length] at hU
    rw [chk7_eq]
    exact List.all_eq_true.1 h7' U hU)

end BeatAvg.K8
