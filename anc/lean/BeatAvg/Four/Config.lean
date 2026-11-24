import BeatAvg.Cert.CfgReal
import Fast.Four.Basic

/-! The existing colored-configuration construction with three ratio cuts. -/
namespace BeatAvg.Four
open MeasureTheory Set Function

abbrev Config := Fast.Four.Config

noncomputable def cut (q : Fin 3) : ℝ :=
  (Fast.Four.cutNum q : ℝ) / (Fast.Four.cutDen q : ℝ)

instance (n : ℕ) : MeasurableSpace (Config n) := ⊤

instance (n : ℕ) : Finite (Config n) :=
  Finite.of_injective (fun c : Config n => (c.additive, c.close)) (by
    intro a b h
    cases a; cases b
    simpa only [Prod.mk.injEq, Fast.Four.Config.mk.injEq] using h)

def Config.comap {m n : ℕ} (c : Config n) (ι : Fin m → Fin n) : Config m :=
  ⟨c.additive.comap ι, fun q i j => c.close q (ι i) (ι j)⟩

open Classical in
noncomputable def configOf {n : ℕ} (v : Fin n → ℝ) : Config n :=
  ⟨cfgOf v, fun q i j => decide (i ≠ j ∧ max (v i) (v j) < cut q * min (v i) (v j))⟩

theorem configOf_comp {m n : ℕ} (v : Fin n → ℝ) (ι : Fin m → Fin n)
    (hι : Injective ι) : configOf (v ∘ ι) = (configOf v).comap ι := by
  simp only [configOf, Config.comap, cfgOf_comp v ι hι, comp_apply, hι.ne_iff]

theorem measurable_configOf {n : ℕ} :
    Measurable (configOf : (Fin n → ℝ) → Config n) := by
  classical
  refine measurable_to_countable' fun c => ?_
  have h : configOf ⁻¹' {c} = (cfgOf ⁻¹' {c.additive}) ∩
      ⋂ q, ⋂ i, ⋂ j, {v : Fin n → ℝ |
        decide (i ≠ j ∧ max (v i) (v j) < cut q * min (v i) (v j)) = c.close q i j} := by
    ext v
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · intro hv
      cases hv
      exact ⟨rfl, fun _ _ _ => rfl⟩
    · rintro ⟨ha, hc⟩
      cases c
      simp only [configOf, Fast.Four.Config.mk.injEq]
      exact ⟨ha, funext fun q => funext fun i => funext fun j => hc q i j⟩
  rw [h]
  refine (measurable_cfgOf (measurableSet_singleton _)).inter ?_
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun i =>
    MeasurableSet.iInter fun j => ?_
  by_cases hij : i = j
  · subst j; simp
  · simpa [ne_eq, hij] using
      (measurableSet_decide_eq
        (measurableSet_lt (show Measurable (fun v : Fin n → ℝ => max (v i) (v j)) by fun_prop)
          (show Measurable (fun v : Fin n → ℝ => cut q * min (v i) (v j)) by fun_prop))
        (c.close q i j))

theorem measurable_of_config {n : ℕ} {β : Type*} [MeasurableSpace β]
    (F : Config n → β) : Measurable F := fun _ _ => trivial

end BeatAvg.Four
