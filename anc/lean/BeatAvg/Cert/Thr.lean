import BeatAvg.Cert.Tab
import Fast.Eval

/-!
# Threshold terms on a sorted sample
-/

open MeasureTheory Set Function

namespace BeatAvg

/-- A sorted sample of eight points in general position. -/
structure SG8 (ω : Fin 8 → ℝ) : Prop where
  mono : StrictMono ω
  nonneg : 0 ≤ ω 0
  noTie : ∀ a b c d : Fin 8, a ≠ d → b ≠ d → c ≠ d → ω a + ω b + ω c ≠ 2 * ω d

theorem sb_cfgOf {n : ℕ} (v : Fin n → ℝ) {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d) :
    (cfgOf v).sb a b c d = true ↔ v a + v b + v c < 2 * v d := by
  simp [cfgOf, hab, hac, hbc, had, hbd, hcd]

theorem lt_cfgOf {n : ℕ} (v : Fin n → ℝ) (i j : Fin n) : (cfgOf v).lt i j = true ↔ v i < v j := by
  simp [cfgOf]

theorem trip_ne (θ : ℕ) : Fast.tripI θ ≠ Fast.tripJ θ ∧ Fast.tripI θ ≠ Fast.tripK θ ∧
    Fast.tripJ θ ≠ Fast.tripK θ := by
  have h4 : θ % 4 < 4 := Nat.mod_lt θ (by norm_num)
  obtain ⟨k, hk⟩ : ∃ k, k = θ % 4 := ⟨_, rfl⟩
  rw [← hk] at h4
  simp only [Fast.tripI, Fast.tripJ, Fast.tripK, ← hk]
  interval_cases k <;> decide

theorem bB_ne_bA (i j : Fin 4) : bB i ≠ bA j := by
  intro h
  have := congrArg Fin.val h
  rw [bB_val, bA_val] at this
  omega

theorem bA_injective : Injective bA := Fin.castAdd_injective 4 4

theorem below_iff {ω : Fin 8 → ℝ} (hω : SG8 ω) {ρ : Fin 8 → Fin 8} (hρ : Injective ρ) (θ : Fin 8)
    (i : Fin 4) :
    Fast.below (cfgOf ω) ρ θ.val (bB i) = true ↔ ω (ρ (bB i)) < tau θ (ω ∘ ρ ∘ bA) := by
  obtain ⟨hIJ, hIK, hJK⟩ := trip_ne θ.val
  have hp : ∀ j, ρ (bB i) ≠ ρ (bA j) := fun j => hρ.ne (bB_ne_bA i j)
  have hr : ∀ {j k : Fin 4}, j ≠ k → ρ (bA j) ≠ ρ (bA k) := fun h => hρ.ne (bA_injective.ne h)
  unfold Fast.below tau
  by_cases h : θ.val < 4
  · simp only [h, if_true]
    change (cfgOf ω).sb (ρ (bB i)) (ρ (bA (Fast.tripI θ.val))) (ρ (bA (Fast.tripK θ.val)))
      (ρ (bA (Fast.tripJ θ.val))) = true ↔ _
    rw [sb_cfgOf ω (hp _) (hp _) (hr hIK) (hp _) (hr hIJ) (hr hJK.symm)]
    simp only [comp_apply]
    constructor <;> intro h' <;> linarith
  · simp only [h, if_false]
    change ((cfgOf ω).lt (ρ (bB i)) (ρ (bA (Fast.tripK θ.val))) ||
      !(cfgOf ω).sb (ρ (bA (Fast.tripI θ.val))) (ρ (bA (Fast.tripJ θ.val)))
        (ρ (bA (Fast.tripK θ.val))) (ρ (bB i))) = true ↔ _
    have hsb := sb_cfgOf ω (hr hIJ) (hr hIK) (hr hJK) (hp _).symm (hp _).symm (hp _).symm
    have htie := hω.noTie _ _ _ _ (hp (Fast.tripI θ.val)).symm (hp (Fast.tripJ θ.val)).symm
      (hp (Fast.tripK θ.val)).symm
    rw [Bool.or_eq_true, lt_cfgOf, Bool.not_eq_true', ← Bool.not_eq_true, hsb, lt_max_iff]
    simp only [comp_apply]
    constructor
    · rintro (h1 | h2)
      · exact Or.inl h1
      · right
        rcases lt_or_gt_of_ne htie with h3 | h3
        · exact absurd h3 h2
        · linarith
    · rintro (h1 | h2)
      · exact Or.inl h1
      · right; intro h3; linarith

theorem ty0_iff {ω : Fin 8 → ℝ} (hω : SG8 ω) {ρ : Fin 8 → Fin 8} (hρ : Injective ρ) :
    Fast.ty0 (cfgOf ω) ρ = true ↔ type0 (ω ∘ ρ ∘ bA) := by
  have h01 : ρ 0 ≠ ρ 1 := hρ.ne (by decide)
  have h02 : ρ 0 ≠ ρ 2 := hρ.ne (by decide)
  have h12 : ρ 1 ≠ ρ 2 := hρ.ne (by decide)
  have h03 : ρ 0 ≠ ρ 3 := hρ.ne (by decide)
  have h13 : ρ 1 ≠ ρ 3 := hρ.ne (by decide)
  have h23 : ρ 2 ≠ ρ 3 := hρ.ne (by decide)
  have htie := hω.noTie _ _ _ _ h03 h13 h23
  unfold Fast.ty0 type0
  rw [Bool.not_eq_true', ← Bool.not_eq_true, sb_cfgOf ω h01 h02 h12 h03 h13 h23]
  change ¬ (ω (ρ 0) + ω (ρ 1) + ω (ρ 2) < 2 * ω (ρ 3)) ↔
    2 * ω (ρ 3) < ω (ρ 0) + ω (ρ 1) + ω (ρ 2)
  constructor
  · intro h
    rcases lt_or_gt_of_ne htie with h3 | h3
    · exact absurd h3 h
    · exact h3
  · intro h h'; linarith

theorem succF_iff (ω : Fin 8 → ℝ) {ρ : Fin 8 → Fin 8} (hρ : Injective ρ) :
    Fast.succF (cfgOf ω) ρ = true ↔ (ω ∘ ρ ∘ bB) ∈ S4 := by
  unfold Fast.succF
  rw [sb_cfgOf ω (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide))
    (hρ.ne (by decide)) (hρ.ne (by decide))]
  rfl

theorem succA_iff (ω : Fin 8 → ℝ) {ρ : Fin 8 → Fin 8} (hρ : Injective ρ) :
    Fast.succA (cfgOf ω) ρ = true ↔ (ω ∘ ρ ∘ bA) ∈ S4 := by
  unfold Fast.succA
  rw [sb_cfgOf ω (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide))
    (hρ.ne (by decide)) (hρ.ne (by decide))]
  rfl

end BeatAvg
