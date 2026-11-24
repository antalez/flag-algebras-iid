import BeatAvg.Cert.CfgReal
import Mathlib.Data.List.GetD

/-!
# Sorted samples in general position and their patterns
-/

namespace BeatAvg

/-- A sorted sample in general position on the indices `< n`:
strictly increasing, nonnegative, no ties. -/
structure SG (n : ℕ) (w : ℕ → ℝ) : Prop where
  mono : ∀ i j, i < j → j < n → w i < w j
  nonneg : 0 ≤ w 0
  noTie : ∀ a b c d, a < n → b < n → c < n → d < n → a ≠ d → b ≠ d → c ≠ d →
    w a + w b + w c ≠ 2 * w d

theorem SG.nonneg' {n : ℕ} {w : ℕ → ℝ} (h : SG n w) {i : ℕ} (hi : i < n) : 0 ≤ w i := by
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · rw [h0]; exact h.nonneg
  · exact h.nonneg.trans (h.mono 0 i h0 hi).le

open Classical in
/-- The trit of an increasing quadruple: the number of successful targets. -/
noncomputable def trit (w : ℕ → ℝ) (q : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  (if w q.1 + w q.2.1 + w q.2.2.1 < 2 * w q.2.2.2 then 1 else 0)
    + (if w q.1 + w q.2.1 + w q.2.2.2 < 2 * w q.2.2.1 then 1 else 0)

/-- The pattern of a sample on `n` points. -/
noncomputable def patArr (n : ℕ) (w : ℕ → ℝ) : Array ℕ := ((Fast.combos n).map (trit w)).toArray

theorem mem_combos {n : ℕ} {q : ℕ × ℕ × ℕ × ℕ} :
    q ∈ Fast.combos n ↔ q.1 < q.2.1 ∧ q.2.1 < q.2.2.1 ∧ q.2.2.1 < q.2.2.2 ∧ q.2.2.2 < n := by
  obtain ⟨a, b, c, d⟩ := q
  simp only [Fast.combos, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨a', ha', b', hb', c', hc', d', hd', h⟩
    split_ifs at h with hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨hlt.1, hlt.2.1, hlt.2.2, hd'⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨a, by omega, b, by omega, c, by omega, d, h4, ?_⟩
    simp [h1, h2, h3]

theorem ofFn_getElem!_nat {n : ℕ} (f : Fin n → ℕ) (k : ℕ) (hk : k < n) :
    (Array.ofFn f)[k]! = f ⟨k, hk⟩ := by
  have hs : k < (Array.ofFn f).size := by simpa using hk
  rw [getElem!_pos (Array.ofFn f) k hs, Array.getElem_ofFn]

/-- The entry of the index table is the position of the quadruple in the list. -/
theorem idxFn_eq (n : ℕ) {x y z d : ℕ} (hx : x < 8) (hy : y < 8) (hz : z < 8) (hd : d < 8)
    (hk : x * 512 + y * 64 + z * 8 + d < 4096) :
    Fast.idxFn n ⟨x * 512 + y * 64 + z * 8 + d, hk⟩ = (Fast.combos n).idxOf (x, y, z, d) := by
  have e1 : (x * 512 + y * 64 + z * 8 + d) / 512 = x := by omega
  have e2 : (x * 512 + y * 64 + z * 8 + d) / 64 % 8 = y := by omega
  have e3 : (x * 512 + y * 64 + z * 8 + d) / 8 % 8 = z := by omega
  have e4 : (x * 512 + y * 64 + z * 8 + d) % 8 = d := by omega
  simp only [Fast.idxFn, Fast.comboIdx, e1, e2, e3, e4]

theorem getElem?_idxOf {α : Type*} [BEq α] [LawfulBEq α] (l : List α) (a : α) (h : a ∈ l) :
    l[l.idxOf a]? = some a := by
  have hi : l.idxOf a < l.length := List.idxOf_lt_length_iff.2 h
  rw [List.getElem?_eq_getElem hi, List.getElem_idxOf hi]

theorem idx8_spec : ∀ x y z d : Fin 8, x < y → y < z → z < d →
    (Fast.combos 8)[Fast.idx8 x.val y.val z.val d.val]? = some (x.val, y.val, z.val, d.val) := by
  intro x y z d hxy hyz hzd
  have hk : x.val * 512 + y.val * 64 + z.val * 8 + d.val < 4096 := by omega
  have h0 : Fast.idx8Tab = Array.ofFn (Fast.idxFn 8) := rfl
  have h1 : Fast.idx8 x.val y.val z.val d.val
      = (Fast.combos 8).idxOf (x.val, y.val, z.val, d.val) := by
    unfold Fast.idx8
    rw [h0, ofFn_getElem!_nat _ _ hk]
    exact idxFn_eq 8 x.isLt y.isLt z.isLt d.isLt hk
  rw [h1]
  exact getElem?_idxOf _ _ (mem_combos.2 ⟨hxy, hyz, hzd, d.isLt⟩)

theorem patArr_idx8 (w : ℕ → ℝ) {x y z d : ℕ} (hxy : x < y) (hyz : y < z) (hzd : z < d)
    (hd : d < 8) : (patArr 8 w)[Fast.idx8 x y z d]! = trit w (x, y, z, d) := by
  have h := idx8_spec ⟨x, by omega⟩ ⟨y, by omega⟩ ⟨z, by omega⟩ ⟨d, hd⟩ hxy hyz hzd
  simp only at h
  simp [patArr, h]

/-- The first indicator is implied by the second. -/
theorem second_imp_first {w : ℕ → ℝ} {x y z d : ℕ} (hzd : w z < w d)
    (h : w x + w y + w d < 2 * w z) : w x + w y + w z < 2 * w d := by linarith

theorem trit_ge_one_iff {w : ℕ → ℝ} {x y z d : ℕ} (hzd : w z < w d) :
    1 ≤ trit w (x, y, z, d) ↔ w x + w y + w z < 2 * w d := by
  unfold trit
  simp only
  constructor
  · intro h
    by_contra hc
    have h2 : ¬ (w x + w y + w d < 2 * w z) := fun h2 => hc (second_imp_first hzd h2)
    simp [hc, h2] at h
  · intro h
    simp [h]

theorem trit_eq_two_iff {w : ℕ → ℝ} {x y z d : ℕ} (hzd : w z < w d) :
    trit w (x, y, z, d) = 2 ↔ w x + w y + w d < 2 * w z := by
  unfold trit
  simp only
  constructor
  · intro h
    by_contra hc
    by_cases h1 : w x + w y + w z < 2 * w d <;> simp [hc, h1] at h
  · intro h
    have h1 := second_imp_first hzd h
    simp [h, h1]

end BeatAvg
