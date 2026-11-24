import BeatAvg.Cert.PatSb
import Fast.Gen

/-!
# Sum bits of a sorted sample from its pattern, for a general number of points
-/

namespace BeatAvg

/-- The index function reads the right entry of the pattern. -/
def IdxOk (n : ℕ) (idx : ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (w : ℕ → ℝ) (x y z d : ℕ), x < y → y < z → z < d → d < n →
    (patArr n w)[idx x y z d]! = trit w (x, y, z, d)

theorem sbCoreG {n : ℕ} {idx : ℕ → ℕ → ℕ → ℕ → ℕ} (hidx : IdxOk n idx) {w : ℕ → ℝ} (hw : SG n w)
    {x y z d : ℕ} (hxy : x < y) (hyz : y < z) (hz : z < n) (hd : d < n) :
    (if z < d then decide (1 ≤ (patArr n w)[idx x y z d]!)
      else if y < d ∧ d < z then decide ((patArr n w)[idx x y d z]! = 2) else false)
    = decide (x ≠ d ∧ y ≠ d ∧ z ≠ d ∧ w x + w y + w z < 2 * w d) := by
  by_cases h1 : z < d
  · rw [if_pos h1, hidx w x y z d hxy hyz h1 hd]
    apply decide_eq_decide.2
    rw [trit_ge_one_iff (hw.mono z d h1 hd)]
    constructor
    · intro h; exact ⟨by omega, by omega, by omega, h⟩
    · intro h; exact h.2.2.2
  · rw [if_neg h1]
    by_cases h2 : y < d ∧ d < z
    · rw [if_pos h2, hidx w x y d z hxy h2.1 h2.2 hz]
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

theorem sbPatG_spec {n : ℕ} {idx : ℕ → ℕ → ℕ → ℕ → ℕ} (hidx : IdxOk n idx) {w : ℕ → ℝ}
    (hw : SG n w) {a b c d : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n) :
    Fast.sbPatG idx (patArr n w) a b c d = decide (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ≠ d ∧ b ≠ d ∧ c ≠ d ∧
      w a + w b + w c < 2 * w d) := by
  obtain ⟨x, hx⟩ : ∃ x, x = min a (min b c) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = max a (max b c) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = a + b + c - x - z := ⟨_, rfl⟩
  have hcases := sort3_cases a b c
  rw [← hx, ← hz, ← hy] at hcases
  have hunf : Fast.sbPatG idx (patArr n w) a b c d =
      if x < y ∧ y < z then
        (if z < d then decide (1 ≤ (patArr n w)[idx x y z d]!)
          else if y < d ∧ d < z then decide ((patArr n w)[idx x y d z]! = 2) else false)
      else false := by
    simp only [Fast.sbPatG, ← hx, ← hz, ← hy]
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
    have hzn : z < n := by rw [hz]; simp only [Nat.max_def]; split_ifs <;> omega
    rw [sbCoreG hidx hw hxy hyz hzn hd]
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

theorem idx7_spec : ∀ x y z d : Fin 7, x < y → y < z → z < d →
    (Fast.combos 7)[Fast.idx7 x.val y.val z.val d.val]? = some (x.val, y.val, z.val, d.val) := by
  intro x y z d hxy hyz hzd
  have hk : x.val * 512 + y.val * 64 + z.val * 8 + d.val < 4096 := by omega
  have h0 : Fast.idx7Tab = Array.ofFn (Fast.idxFn 7) := rfl
  have h1 : Fast.idx7 x.val y.val z.val d.val
      = (Fast.combos 7).idxOf (x.val, y.val, z.val, d.val) := by
    unfold Fast.idx7
    rw [h0, ofFn_getElem!_nat _ _ hk]
    exact idxFn_eq 7 (by omega) (by omega) (by omega) (by omega) hk
  rw [h1]
  exact getElem?_idxOf _ _ (mem_combos.2 ⟨hxy, hyz, hzd, d.isLt⟩)

theorem idxOk7 : IdxOk 7 Fast.idx7 := by
  intro w x y z d hxy hyz hzd hd
  have h := idx7_spec ⟨x, by omega⟩ ⟨y, by omega⟩ ⟨z, by omega⟩ ⟨d, hd⟩ hxy hyz hzd
  simp only at h
  simp [patArr, h]

end BeatAvg
