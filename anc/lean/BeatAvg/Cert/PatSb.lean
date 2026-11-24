import BeatAvg.Cert.PatReal

/-!
# The sum bits of a sorted sample are read off its pattern
-/

namespace BeatAvg

theorem sbCore {w : ℕ → ℝ} (hw : SG 8 w) {x y z d : ℕ} (hxy : x < y) (hyz : y < z) (hz : z < 8)
    (hd : d < 8) :
    (if z < d then decide (1 ≤ (patArr 8 w)[Fast.idx8 x y z d]!)
      else if y < d ∧ d < z then decide ((patArr 8 w)[Fast.idx8 x y d z]! = 2) else false)
    = decide (x ≠ d ∧ y ≠ d ∧ z ≠ d ∧ w x + w y + w z < 2 * w d) := by
  by_cases h1 : z < d
  · rw [if_pos h1, patArr_idx8 w hxy hyz h1 hd]
    apply decide_eq_decide.2
    rw [trit_ge_one_iff (hw.mono z d h1 hd)]
    constructor
    · intro h; exact ⟨by omega, by omega, by omega, h⟩
    · intro h; exact h.2.2.2
  · rw [if_neg h1]
    by_cases h2 : y < d ∧ d < z
    · rw [if_pos h2, patArr_idx8 w hxy h2.1 h2.2 hz]
      apply decide_eq_decide.2
      rw [trit_eq_two_iff (hw.mono d z h2.2 hz)]
      constructor
      · intro h; exact ⟨by omega, by omega, by omega, h⟩
      · intro h; exact h.2.2.2
    · rw [if_neg h2]
      symm
      rw [decide_eq_false_iff_not]
      rintro ⟨hx, hy, hz', hS⟩
      have hdy : d < y := by omega
      have e1 := hw.mono d y hdy (by omega)
      have e2 := hw.mono d z (by omega) hz
      have e3 := hw.nonneg' (i := x) (by omega)
      linarith

theorem sort3_cases (a b c : ℕ) :
    ((a = b ∨ a = c ∨ b = c) ∧
      ¬ (min a (min b c) < a + b + c - min a (min b c) - max a (max b c) ∧
        a + b + c - min a (min b c) - max a (max b c) < max a (max b c))) ∨
    (min a (min b c) < a + b + c - min a (min b c) - max a (max b c) ∧
      a + b + c - min a (min b c) - max a (max b c) < max a (max b c) ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) := by
  simp only [Nat.min_def, Nat.max_def]
  split_ifs <;> omega

theorem sbPat_spec {w : ℕ → ℝ} (hw : SG 8 w) {a b c d : ℕ} (ha : a < 8) (hb : b < 8) (hc : c < 8)
    (hd : d < 8) :
    Fast.sbPat (patArr 8 w) a b c d = decide (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ≠ d ∧ b ≠ d ∧ c ≠ d ∧
      w a + w b + w c < 2 * w d) := by
  obtain ⟨x, hx⟩ : ∃ x, x = min a (min b c) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = max a (max b c) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = a + b + c - x - z := ⟨_, rfl⟩
  have hcases := sort3_cases a b c
  rw [← hx, ← hz, ← hy] at hcases
  have hunf : Fast.sbPat (patArr 8 w) a b c d =
      if x < y ∧ y < z then
        (if z < d then decide (1 ≤ (patArr 8 w)[Fast.idx8 x y z d]!)
          else if y < d ∧ d < z then decide ((patArr 8 w)[Fast.idx8 x y d z]! = 2) else false)
      else false := by
    simp only [Fast.sbPat, ← hx, ← hz, ← hy]
  rw [hunf]
  rcases hcases with ⟨heq, hnot⟩ | ⟨hxy, hyz, hab, hac, hbc⟩
  · rw [if_neg hnot]
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨h1, h2, h3, -⟩
    rcases heq with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
  · rw [if_pos ⟨hxy, hyz⟩]
    have hz8 : z < 8 := by rw [hz]; simp only [Nat.max_def]; split_ifs <;> omega
    rw [sbCore hw hxy hyz hz8 hd]
    -- (x, y, z) is a permutation of (a, b, c)
    have hperm : (x = a ∧ y = b ∧ z = c) ∨ (x = a ∧ y = c ∧ z = b) ∨ (x = b ∧ y = a ∧ z = c) ∨
        (x = b ∧ y = c ∧ z = a) ∨ (x = c ∧ y = a ∧ z = b) ∨ (x = c ∧ y = b ∧ z = a) := by
      rw [hy, hx, hz]
      simp only [Nat.min_def, Nat.max_def]
      split_ifs <;> omega
    apply decide_eq_decide.2
    rcases hperm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
      first
        | exact ⟨hab, hac, hbc, by omega, by omega, by omega, by linarith⟩
        | exact ⟨by tauto, by tauto, by tauto, by linarith [h4.2.2.2]⟩

end BeatAvg
