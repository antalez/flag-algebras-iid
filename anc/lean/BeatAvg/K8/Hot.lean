import Mathlib.Data.List.GetD
import BeatAvg.K8.Bits
import BeatAvg.K8.Eval

/-!
# The one-hot form of a pattern: a conjunction of conditions on trits is one `land`
-/

namespace BeatAvg.K8

/-- One-hot form of a list of trits. -/
def hotL : List ℕ → ℕ
  | [] => 0
  | t :: l => 2 ^ t + 8 * hotL l

theorem hotN_packL : ∀ (xs : List ℕ), Small xs → hotN xs.length (packL xs) = hotL xs
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h.head
    have ih := hotN_packL xs h.tail
    have e1 : (x + 4 * packL xs) / 4 = packL xs := by omega
    have e2 : (x + 4 * packL xs) % 4 = x := by omega
    simp only [List.length_cons, hotN, packL_cons, nadd, nmul, nmod, ndiv, nshl, e1, e2, ih, hotL,
      Nat.one_shiftLeft]

theorem testBit_hotL : ∀ (xs : List ℕ), (∀ t ∈ xs, t ≤ 2) → ∀ i : ℕ,
    (hotL xs).testBit i = decide (i / 3 < xs.length ∧ i % 3 = xs.getD (i / 3) 0)
  | [], _, i => by simp [hotL]
  | t :: xs, h, i => by
    have ht : t ≤ 2 := h t List.mem_cons_self
    have ih := testBit_hotL xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have e : hotL (t :: xs) = 2 ^ 3 * hotL xs + 2 ^ t := by simp only [hotL]; ring
    have hlt : 2 ^ t < 2 ^ 3 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [e, Nat.testBit_two_pow_mul_add _ hlt]
    by_cases hi : i < 3
    · rw [ite_eq_left hi, Nat.testBit_two_pow]
      have h0 : i / 3 = 0 := by omega
      have h1 : i % 3 = i := by omega
      simp only [h0, h1, List.length_cons, List.getD_cons_zero]
      apply decide_eq_decide.2
      constructor
      · intro h; exact ⟨by omega, h.symm⟩
      · intro h; exact h.2.symm
    · rw [ite_eq_right hi, ih]
      have h0 : i / 3 = (i - 3) / 3 + 1 := by omega
      have h1 : i % 3 = (i - 3) % 3 := by omega
      rw [h0, h1, List.length_cons, List.getD_cons_succ]
      apply decide_eq_decide.2
      constructor
      · intro h; exact ⟨by omega, h.2⟩
      · intro h; exact ⟨by omega, h.2⟩

/-- The condition "trit `p` is not in the set `c`" as a test on the one-hot form. -/
theorem clear_atom {xs : List ℕ} (hx : ∀ t ∈ xs, t ≤ 2) {p c : ℕ} (hp : p < xs.length)
    (hc : c < 8) : hotL xs &&& (c <<< (3 * p)) = 0 ↔ c.testBit (xs.getD p 0) = false := by
  have ht : xs.getD p 0 ≤ 2 := by
    rw [List.getD_eq_getElem _ _ hp]; exact hx _ (List.getElem_mem hp)
  constructor
  · intro h
    obtain ⟨t, htdef⟩ : ∃ t, t = xs.getD p 0 := ⟨_, rfl⟩
    rw [← htdef] at ht ⊢
    have e1 : (3 * p + t) / 3 = p := by omega
    have e2 : (3 * p + t) % 3 = t := by omega
    have e3 : 3 * p + t - 3 * p = t := by omega
    have hH : (hotL xs).testBit (3 * p + t) = true := by
      rw [testBit_hotL xs hx, e1, e2, decide_eq_true_eq]
      exact ⟨hp, htdef⟩
    have hb : (hotL xs &&& (c <<< (3 * p))).testBit (3 * p + t) = false := by
      rw [h]; exact Nat.zero_testBit _
    rw [Nat.testBit_and, hH, Bool.true_and, Nat.testBit_shiftLeft, e3] at hb
    simpa using hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_shiftLeft, testBit_hotL xs hx]
    by_contra hne
    simp only [Bool.and_eq_false_iff, not_or, Bool.not_eq_false, decide_eq_true_eq, ge_iff_le] at hne
    obtain ⟨⟨-, hmod⟩, hge, hbit⟩ := hne
    have hlt : i - 3 * p < 3 := by
      by_contra hcon
      have : c < 2 ^ (i - 3 * p) := lt_of_lt_of_le hc
        (by calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (i - 3 * p) := Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow this] at hbit
      exact absurd hbit (by simp)
    have e1 : i / 3 = p := by omega
    have e2 : i % 3 = i - 3 * p := by omega
    rw [e1, e2] at hmod
    rw [hmod, h] at hbit
    exact absurd hbit (by simp)

theorem clear_lor (H f g : ℕ) : H &&& (f ||| g) = 0 ↔ H &&& f = 0 ∧ H &&& g = 0 := by
  rw [Nat.and_or_distrib_left, Nat.or_eq_zero_iff]

theorem clear_zero (H : ℕ) : H &&& 0 = 0 := Nat.and_zero H

end BeatAvg.K8
