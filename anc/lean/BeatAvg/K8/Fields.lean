import Mathlib.Tactic
import BeatAvg.K8.Bits

/-!
# Sums of packed entries

An entry packs `K` fields of `w` bits. If the fields of the entries are small enough, the fields of
a sum of entries are the sums of the fields.
-/

namespace BeatAvg.K8

/-- Field `k` of width `w`. -/
def fieldAt (w a k : ℕ) : ℕ := Nat.mod (Nat.shiftRight a (Nat.mul w k)) (Nat.pow 2 w)

theorem fieldAt_eq (w a k : ℕ) : fieldAt w a k = a / (2 ^ w) ^ k % 2 ^ w := by
  simp only [fieldAt, nmod, nshr, nmul, npow, Nat.shiftRight_eq_div_pow, pow_mul]

/-- `K` fields of `w` bits, each below `2 ^ w0`. -/
def Ent (w w0 K e : ℕ) : Prop := e < (2 ^ w) ^ K ∧ ∀ k < K, fieldAt w e k < 2 ^ w0

theorem digit_add (B : ℕ) (hB : 0 < B) : ∀ (K a b : ℕ), a < B ^ K → b < B ^ K →
    (∀ k < K, a / B ^ k % B + b / B ^ k % B < B) →
    a + b < B ^ K ∧ ∀ k < K, (a + b) / B ^ k % B = a / B ^ k % B + b / B ^ k % B
  | 0, a, b, ha, hb, _ => by
    simp only [pow_zero, Nat.lt_one_iff] at ha hb
    subst ha; subst hb
    exact ⟨by simp, fun k hk => absurd hk (by omega)⟩
  | K + 1, a, b, ha, hb, h => by
    have h0 := h 0 (by omega)
    simp only [pow_zero, Nat.div_one] at h0
    have ha' : a / B < B ^ K := by
      rw [Nat.div_lt_iff_lt_mul hB]; rwa [pow_succ] at ha
    have hb' : b / B < B ^ K := by
      rw [Nat.div_lt_iff_lt_mul hB]; rwa [pow_succ] at hb
    have hrec := digit_add B hB K (a / B) (b / B) ha' hb' (fun k hk => by
      have := h (k + 1) (by omega)
      rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this)
    have hdiv : (a + b) / B = a / B + b / B := by
      have ea := Nat.div_add_mod a B
      have eb := Nat.div_add_mod b B
      have : a + b = (a % B + b % B) + B * (a / B + b / B) := by ring_nf; ring_nf at ea eb; omega
      rw [this, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt h0, zero_add]
    have hmod : (a + b) % B = a % B + b % B := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt h0]
    refine ⟨?_, ?_⟩
    · have ea := Nat.div_add_mod (a + b) B
      rw [pow_succ]
      have : (a + b) / B < B ^ K := by rw [hdiv]; exact hrec.1
      have hm : (a + b) % B < B := Nat.mod_lt _ hB
      nlinarith
    · intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simpa using hmod
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have := hrec.2 k' (by omega)
        rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
          ← Nat.div_div_eq_div_mul, hdiv]
        exact this

/-- The fields of a sum of entries are the sums of the fields. -/
theorem fields_sum {w w0 K : ℕ} : ∀ (es : List ℕ), (∀ e ∈ es, Ent w w0 K e) →
    es.length * 2 ^ w0 ≤ 2 ^ w →
    es.sum < (2 ^ w) ^ K ∧ ∀ k < K, fieldAt w es.sum k = (es.map fun e => fieldAt w e k).sum
  | [], _, _ => by
    refine ⟨by simp, fun k _ => ?_⟩
    simp [fieldAt_eq]
  | e :: es, h, hlen => by
    have he := h e List.mem_cons_self
    have hes := fields_sum es (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (le_trans (Nat.mul_le_mul_right _ (by simp)) hlen)
    have hB : 0 < 2 ^ w := by positivity
    have hbound : ∀ k < K, (es.map fun e => fieldAt w e k).sum ≤ es.length * (2 ^ w0 - 1) := by
      intro k hk
      have : ∀ (l : List ℕ), (∀ x ∈ l, Ent w w0 K x) →
          (l.map fun e => fieldAt w e k).sum ≤ l.length * (2 ^ w0 - 1) := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons a l ih =>
          intro hl
          have ha := (hl a List.mem_cons_self).2 k hk
          have := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          have : fieldAt w a k ≤ 2 ^ w0 - 1 := by omega
          nlinarith
      exact this es fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hpos : 0 < 2 ^ w0 := by positivity
    have hadd := digit_add (2 ^ w) hB K e es.sum he.1 hes.1 (fun k hk => by
      have h1 := he.2 k hk
      have h2 := hbound k hk
      rw [← fieldAt_eq, ← fieldAt_eq, hes.2 k hk]
      simp only [List.length_cons] at hlen
      have : es.length * (2 ^ w0 - 1) + 2 ^ w0 ≤ (es.length + 1) * 2 ^ w0 := by
        have : es.length * (2 ^ w0 - 1) ≤ es.length * 2 ^ w0 := Nat.mul_le_mul_left _ (by omega)
        nlinarith
      omega)
    rw [List.sum_cons]
    refine ⟨hadd.1, fun k hk => ?_⟩
    rw [fieldAt_eq, hadd.2 k hk, ← fieldAt_eq, ← fieldAt_eq, hes.2 k hk, List.map_cons,
      List.sum_cons]

end BeatAvg.K8
