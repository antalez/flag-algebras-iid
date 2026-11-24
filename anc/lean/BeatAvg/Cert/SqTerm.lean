import BeatAvg.Cert.DegInv

/-!
# The square part on a sorted sample
-/

open MeasureTheory Set Function

namespace BeatAvg

theorem sel2_injective : Injective Fast.sel2 := by decide

theorem pts23_eval1 {ω : Fin 8 → ℝ} (hω : SG8 ω) {ρ : Fin 8 → Fin 8} (hR : Monotone (ρ ∘ bR))
    (hT : Monotone (ρ ∘ bT)) :
    pts23 ((ω ∘ ρ) ∘ bR, (ω ∘ ρ) ∘ bT) = ω ∘ (ρ ∘ Fast.first5) := by
  have h1 : sortT ((ω ∘ ρ) ∘ bR) = (ω ∘ ρ) ∘ bR := sortT_of_monotone (hω.mono.monotone.comp hR)
  have h2 : sortT ((ω ∘ ρ) ∘ bT) = (ω ∘ ρ) ∘ bT := sortT_of_monotone (hω.mono.monotone.comp hT)
  unfold pts23
  simp only [h1, h2]
  funext i
  refine Fin.addCases (m := 2) (n := 3)
    (motive := fun i => Fin.append ((ω ∘ ρ) ∘ bR) ((ω ∘ ρ) ∘ bT) i = (ω ∘ (ρ ∘ Fast.first5)) i)
    (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    show ω (ρ (bR j)) = ω (ρ (Fast.first5 (Fin.castAdd 3 j)))
    have : bR j = Fast.first5 (Fin.castAdd 3 j) := Fin.ext rfl
    rw [this]
  · rw [Fin.append_right]
    show ω (ρ (bT j)) = ω (ρ (Fast.first5 (Fin.natAdd 2 j)))
    have : bT j = Fast.first5 (Fin.natAdd 2 j) := Fin.ext rfl
    rw [this]

theorem pts23_eval2 {ω : Fin 8 → ℝ} (hω : SG8 ω) {ρ : Fin 8 → Fin 8} (hR : Monotone (ρ ∘ bR))
    (hT' : Monotone (ρ ∘ bT')) :
    pts23 ((ω ∘ ρ) ∘ bR, (ω ∘ ρ) ∘ bT') = ω ∘ (ρ ∘ Fast.sel2) := by
  have h1 : sortT ((ω ∘ ρ) ∘ bR) = (ω ∘ ρ) ∘ bR := sortT_of_monotone (hω.mono.monotone.comp hR)
  have h2 : sortT ((ω ∘ ρ) ∘ bT') = (ω ∘ ρ) ∘ bT' :=
    sortT_of_monotone (hω.mono.monotone.comp hT')
  unfold pts23
  simp only [h1, h2]
  funext i
  refine Fin.addCases (m := 2) (n := 3)
    (motive := fun i => Fin.append ((ω ∘ ρ) ∘ bR) ((ω ∘ ρ) ∘ bT') i = (ω ∘ (ρ ∘ Fast.sel2)) i)
    (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    show ω (ρ (bR j)) = ω (ρ (Fast.sel2 (Fin.castAdd 3 j)))
    have : bR j = Fast.sel2 (Fin.castAdd 3 j) := by
      fin_cases j <;> rfl
    rw [this]
  · rw [Fin.append_right]
    show ω (ρ (bT' j)) = ω (ρ (Fast.sel2 (Fin.natAdd 2 j)))
    have : bT' j = Fast.sel2 (Fin.natAdd 2 j) := by
      fin_cases j <;> rfl
    rw [this]

theorem sqPart_eval (T : Tab) {ω : Fin 8 → ℝ} (hω : SG8 ω) {ρ : Fin 8 → Fin 8} (hρ : Injective ρ)
    (hR : Monotone (ρ ∘ bR)) (hT : Monotone (ρ ∘ bT)) (hT' : Monotone (ρ ∘ bT')) :
    sqPart T (ω ∘ ρ) = sqR T (cfgOf ω) ρ := by
  unfold sqPart sqR
  rw [split3_e233, sqK_tab, pts23_eval1 hω hR hT, pts23_eval2 hω hR hT',
    cfgOf_comp ω _ (hρ.comp first5_injective), cfgOf_comp ω _ (hρ.comp sel2_injective)]

end BeatAvg
