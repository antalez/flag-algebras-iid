module
public import LeanProofs.FiniteLaw
public import LeanProofs.LadderGeometry
set_option linter.style.header false
@[expose] public section
noncomputable section
open scoped BigOperators Classical

namespace Endpoint
namespace Ladder

abbrev Atom (n : ℕ) := Option (Option (Fin n))

def location {n : ℕ} : Atom n → ℝ
  | none => 0
  | some none => 1
  | some (some i) => rung (i.val + 1)

def mass {n : ℕ} (p q u : ℝ) : Atom n → ℝ
  | none => p
  | some none => q
  | some (some _) => u

abbrev pairGood {n : ℕ} : Option (Fin n) → Option (Fin n) → Option (Fin n) → Prop
  | some _, some _, none => False
  | _, _, _ => True

abbrev good {n : ℕ} : Atom n → Atom n → Atom n → Atom n → Prop
  | _, _, _, none => False
  | none, none, _, some _ => True
  | none, some _, none, some _ => True
  | some _, none, none, some _ => True
  | none, some a, some b, some t => pairGood a b t
  | some a, none, some b, some t => pairGood a b t
  | some a, some b, none, some t => pairGood a b t
  | some none, some none, some none, some (some _) => True
  | some (some i), some none, some none, some (some j) => i < j
  | some none, some (some i), some none, some (some j) => i < j
  | some none, some none, some (some i), some (some j) => i < j
  | _, _, _, _ => False

theorem positive_location_bounds {n : ℕ} (i : Option (Fin n)) :
    1 ≤ location (some i) ∧ location (some i) < Real.sqrt 2 := by
  cases i with
  | none => exact ⟨le_rfl, sqrt_two_gt_one⟩
  | some i => exact ⟨one_le_rung _, rung_lt_sqrt _⟩

theorem single_good {n : ℕ} (i t : Option (Fin n)) :
    location (some i) < kappa * location (some t) := by
  have hi := positive_location_bounds i
  have ht := positive_location_bounds t
  have hc := kappa_pos
  unfold kappa at *
  nlinarith

theorem pair_good {n : ℕ} (i j t : Option (Fin n)) (h : pairGood i j t) :
    location (some i) + location (some j) < kappa * location (some t) := by
  have hi := positive_location_bounds i
  have hj := positive_location_bounds j
  cases t with
  | some t =>
    have ht := three_lt_target t.val
    have hs := sqrt_two_lt_three_halves
    change _ < kappa * rung (t.val + 1)
    linarith
  | none =>
    cases i <;> cases j <;> simp_all [pairGood, location, kappa]
    linarith

theorem good_wins {n : ℕ} (a b d t : Atom n) (h : good a b d t) :
    location a + location b + location d < kappa * location t := by
  cases t with
  | none => simp [good] at h
  | some t =>
    cases a with
    | none =>
      cases b with
      | none =>
        cases d with
        | none =>
          have ht := (positive_location_bounds t).1
          have hc := kappa_pos
          change 0 + 0 + 0 < kappa * location (some t)
          nlinarith
        | some d => simpa [location] using single_good d t
      | some b =>
        cases d with
        | none => simpa [location] using single_good b t
        | some d => simpa [location] using pair_good b d t h
    | some a =>
      cases b with
      | none =>
        cases d with
        | none => simpa [location] using single_good a t
        | some d => simpa [location] using pair_good a d t h
      | some b =>
        cases d with
        | none => simpa [location] using pair_good a b t h
        | some d =>
          cases a <;> cases b <;> cases d <;> cases t <;>
            simp only [good] at h
          · simpa [location, show (1 : ℝ) + 1 + 1 = 3 by norm_num] using three_lt_target _
          all_goals
            have hh := rung_skip (Nat.add_lt_add_right h 1)
            simp only [location]
            linarith

theorem sum_lt_uniform (n : ℕ) (u : ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then u * u else 0) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 * u ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, ↓reduceIte,
      show ∀ x : Fin n, ¬ Fin.last n < x.castSucc by intro x; exact not_lt_of_ge (Fin.le_last _),
      lt_self_iff_false, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_add_distrib, ih]
    simp
    ring

def F (p q r : ℝ) : ℝ :=
  p ^ 3 * (q + r) + 3 * p ^ 2 * (q + r) ^ 2 +
  3 * p * (q ^ 3 + 3 * q ^ 2 * r + 2 * q * r ^ 2 + r ^ 3) +
  q ^ 3 * r + (3 / 2 : ℝ) * q ^ 2 * r ^ 2

def FN (p q r : ℝ) (n : ℕ) : ℝ := F p q r - (3 / 2 : ℝ) * q ^ 2 * r ^ 2 / n

theorem count_good (n : ℕ) (p q u : ℝ) :
    (∑ a : Atom n, ∑ b : Atom n, ∑ d : Atom n, ∑ t : Atom n,
      if good a b d t then mass p q u a * mass p q u b * mass p q u d * mass p q u t
      else 0) = F p q (n * u) - (3 / 2 : ℝ) * q ^ 2 * n * u ^ 2 := by
  simp only [Fintype.sum_option, good, pairGood, mass, ↓reduceIte,
    Finset.sum_const_zero, add_zero, zero_add]
  simp only [show ∀ i j : Fin n,
    (if i < j then u * q * q * u else 0) = q ^ 2 * (if i < j then u * u else 0) by
      intros; split_ifs <;> ring,
    show ∀ i j : Fin n,
    (if i < j then q * u * q * u else 0) = q ^ 2 * (if i < j then u * u else 0) by
      intros; split_ifs <;> ring,
    show ∀ i j : Fin n,
    (if i < j then q * q * u * u else 0) = q ^ 2 * (if i < j then u * u else 0) by
      intros; split_ifs <;> ring]
  simp only [← Finset.mul_sum, sum_lt_uniform, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold F
  ring

def law (n : ℕ) (hn : 0 < n) (p q r : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (ht : p + q + r = 1) : Law (Atom n) where
  x := location
  w := mass p q (r / n)
  x_nonneg i := by
    rcases i with _ | (_ | i)
    · exact le_rfl
    · norm_num [location]
    · exact rung_nonneg _
  w_nonneg i := by
    rcases i with _ | (_ | i)
    · exact hp
    · exact hq
    · exact div_nonneg hr (Nat.cast_nonneg _)
  total := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    simp [Fintype.sum_option, mass, mul_div_cancel₀ _ hn']
    linarith

theorem law_lower (n : ℕ) (hn : 0 < n) (p q r : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (ht : p + q + r = 1) :
    FN p q r n ≤ (law n hn p q r hp hq hr ht).prob kappa := by
  let L := law n hn p q r hp hq hr ht
  have ha := L.accepted_le kappa
    (fun a : Quad (Atom n) => good a.1 a.2.1 a.2.2.1 a.2.2.2)
    (fun a h => good_wins _ _ _ _ h)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc : (∑ a : Quad (Atom n),
      if good a.1 a.2.1 a.2.2.1 a.2.2.2 then L.weight a else 0) = FN p q r n := by
    simp only [Law.weight, L, law, Fintype.sum_prod_type]
    rw [count_good]
    unfold FN
    rw [mul_div_cancel₀ r hn']
    field_simp
  rwa [hc] at ha

end Ladder
end Endpoint
