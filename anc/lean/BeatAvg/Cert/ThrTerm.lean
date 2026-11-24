import BeatAvg.Cert.Thr

/-!
# Value of the threshold part of the functional on a sorted sample
-/

open MeasureTheory Set Function

namespace BeatAvg

theorem ind_eq_ite_bool {α : Type*} [MeasurableSpace α] {s : Set α} {p : α} {b : Bool}
    (h : p ∈ s ↔ b = true) : ind s p = if b then 1 else 0 := by
  cases b
  · rw [ind_of_notMem (by simpa using h)]; rfl
  · rw [ind_of_mem (by simpa using h)]; rfl

/-- The threshold part of `lam`. -/
noncomputable def thrPart (T : Tab) (x : ℝ) (v : Fin 8 → ℝ) : ℝ :=
  ∑ θ, (thr1K T.D θ x (split e44 v) + thr2K T.D θ (split e44 v))

/-- The threshold part, evaluated from a configuration. -/
noncomputable def thrR (T : Tab) (c : Fast.Cfg 8) (ρ : Fin 8 → Fin 8) (x : ℝ) : ℝ :=
  if Fast.ty0 c ρ then
    ∑ θ : Fin 8,
      (T.w1 θ.val * (x * (if Fast.allBelow c ρ θ.val then 1 else 0)
          - (if Fast.succF c ρ && Fast.allBelow c ρ θ.val then 1 else 0))
        + T.w2 θ.val * ((if Fast.succF c ρ && Fast.below c ρ θ.val 7 then 1 else 0)
          - T.clo * (if Fast.allBelow c ρ θ.val then 1 else 0)))
  else 0

theorem allBelow_iff {ω : Fin 8 → ℝ} (hω : SG8 ω) {ρ : Fin 8 → Fin 8} (hρ : Injective ρ)
    (θ : Fin 8) :
    Fast.allBelow (cfgOf ω) ρ θ.val = true ↔ ∀ i, (ω ∘ ρ ∘ bB) i < tau θ (ω ∘ ρ ∘ bA) := by
  have h0 := below_iff hω hρ θ 0
  have h1 := below_iff hω hρ θ 1
  have h2 := below_iff hω hρ θ 2
  have h3 := below_iff hω hρ θ 3
  unfold Fast.allBelow
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  change ((Fast.below (cfgOf ω) ρ θ.val (bB 0) = true ∧ Fast.below (cfgOf ω) ρ θ.val (bB 1) = true) ∧
    Fast.below (cfgOf ω) ρ θ.val (bB 2) = true) ∧ Fast.below (cfgOf ω) ρ θ.val (bB 3) = true ↔ _
  rw [h0, h1, h2, h3]
  constructor
  · rintro ⟨⟨⟨a, b⟩, c⟩, d⟩ i
    fin_cases i
    exacts [a, b, c, d]
  · intro h
    exact ⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩

theorem thrPart_eval (T : Tab) {ω : Fin 8 → ℝ} (hω : SG8 ω) {ρ : Fin 8 → Fin 8} (hρ : Injective ρ)
    (hmono : Monotone (ρ ∘ bA)) (x : ℝ) :
    thrPart T x (ω ∘ ρ) = thrR T (cfgOf ω) ρ x := by
  classical
  have hsort : sortT ((ω ∘ ρ) ∘ bA) = ω ∘ ρ ∘ bA :=
    sortT_of_monotone (hω.mono.monotone.comp hmono)
  have hτ : ∀ θ, T.D.τ θ ((ω ∘ ρ) ∘ bA) = tau θ (ω ∘ ρ ∘ bA) := fun θ => by
    show tau θ (sortT ((ω ∘ ρ) ∘ bA)) = _
    rw [hsort]
  have hA1 : ∀ θ : Fin 8, ind (A1 T.D θ) ((ω ∘ ρ) ∘ bA, (ω ∘ ρ) ∘ bB)
      = if Fast.allBelow (cfgOf ω) ρ θ.val then 1 else 0 := fun θ => by
    apply ind_eq_ite_bool
    rw [allBelow_iff hω hρ θ]
    show (∀ i, ((ω ∘ ρ) ∘ bB) i < T.D.τ θ ((ω ∘ ρ) ∘ bA)) ↔ _
    rw [hτ]; rfl
  have hA2 : ∀ θ : Fin 8, ind (A2 T.D θ) ((ω ∘ ρ) ∘ bA, (ω ∘ ρ) ∘ bB)
      = if Fast.succF (cfgOf ω) ρ && Fast.allBelow (cfgOf ω) ρ θ.val then 1 else 0 := fun θ => by
    apply ind_eq_ite_bool
    rw [Bool.and_eq_true, allBelow_iff hω hρ θ, succF_iff ω hρ]
    show ((ω ∘ ρ) ∘ bB ∈ S4 ∧ ∀ i, ((ω ∘ ρ) ∘ bB) i < T.D.τ θ ((ω ∘ ρ) ∘ bA)) ↔ _
    rw [hτ]; rfl
  have hA3 : ∀ θ : Fin 8, ind (A3 T.D θ) ((ω ∘ ρ) ∘ bA, (ω ∘ ρ) ∘ bB)
      = if Fast.succF (cfgOf ω) ρ && Fast.below (cfgOf ω) ρ θ.val 7 then 1 else 0 := fun θ => by
    apply ind_eq_ite_bool
    rw [Bool.and_eq_true, succF_iff ω hρ]
    have h3 := below_iff hω hρ θ 3
    change Fast.below (cfgOf ω) ρ θ.val 7 = true ↔ _ at h3
    rw [h3]
    show ((ω ∘ ρ) ∘ bB ∈ S4 ∧ ((ω ∘ ρ) ∘ bB) 3 < T.D.τ θ ((ω ∘ ρ) ∘ bA)) ↔ _
    rw [hτ]; rfl
  have hu1 : ∀ θ : Fin 8, T.D.u1 θ ((ω ∘ ρ) ∘ bA)
      = if Fast.ty0 (cfgOf ω) ρ then T.w1 θ.val else 0 := fun θ => by
    show (if type0 (sortT ((ω ∘ ρ) ∘ bA)) then T.w1 θ.val else 0) = _
    rw [hsort]
    by_cases h : type0 (ω ∘ ρ ∘ bA)
    · rw [if_pos h, if_pos ((ty0_iff hω hρ).2 h)]
    · rw [if_neg h, if_neg (fun h' => h ((ty0_iff hω hρ).1 h'))]
  have hu2 : ∀ θ : Fin 8, T.D.u2 θ ((ω ∘ ρ) ∘ bA)
      = if Fast.ty0 (cfgOf ω) ρ then T.w2 θ.val else 0 := fun θ => by
    show (if type0 (sortT ((ω ∘ ρ) ∘ bA)) then T.w2 θ.val else 0) = _
    rw [hsort]
    by_cases h : type0 (ω ∘ ρ ∘ bA)
    · rw [if_pos h, if_pos ((ty0_iff hω hρ).2 h)]
    · rw [if_neg h, if_neg (fun h' => h ((ty0_iff hω hρ).1 h'))]
  unfold thrPart thrR
  simp only [split_e44, thr1K, thr2K, hA1, hA2, hA3, hu1, hu2]
  have hclo : T.D.clo = T.clo := rfl
  rw [hclo]
  by_cases h : Fast.ty0 (cfgOf ω) ρ = true
  · simp only [h, if_true]
  · simp only [h, if_false, Bool.false_eq_true, zero_mul, add_zero, Finset.sum_const_zero]

end BeatAvg
