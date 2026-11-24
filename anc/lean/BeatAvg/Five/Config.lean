import BeatAvg.Cert.CfgReal
import Fast.Five.Config

/-! Pair-colored configurations. The old additive configuration remains unchanged. -/
namespace BeatAvg.Five

open MeasureTheory Set Function

/-- Additive and order data, together with the symmetric pair color used by the
five-point certificate. -/
abbrev Config := Fast.Five.Config

instance (n : ℕ) : MeasurableSpace (Config n) := ⊤

instance (n : ℕ) : Finite (Config n) :=
  Finite.of_injective (fun c : Config n => (c.additive, c.close)) (by
    intro a b h
    cases a; cases b
    simpa only [Prod.mk.injEq, Fast.Five.Config.mk.injEq] using h)

def Config.comap {m n : ℕ} (c : Config n) (ι : Fin m → Fin n) : Config m :=
  ⟨c.additive.comap ι, fun i j => c.close (ι i) (ι j)⟩

open Classical in
noncomputable def configOf {n : ℕ} (v : Fin n → ℝ) : Config n :=
  ⟨cfgOf v, fun i j => decide (i ≠ j ∧ max (v i) (v j) < 2 * min (v i) (v j))⟩

theorem configOf_comp {m n : ℕ} (v : Fin n → ℝ) (ι : Fin m → Fin n)
    (hι : Injective ι) : configOf (v ∘ ι) = (configOf v).comap ι := by
  simp only [configOf, Config.comap, cfgOf_comp v ι hι, comp_apply, hι.ne_iff]

theorem measurable_configOf {n : ℕ} :
    Measurable (configOf : (Fin n → ℝ) → Config n) := by
  classical
  refine measurable_to_countable' fun c => ?_
  have h : configOf ⁻¹' {c} = (cfgOf ⁻¹' {c.additive}) ∩
      ⋂ i, ⋂ j, {v : Fin n → ℝ |
        decide (i ≠ j ∧ max (v i) (v j) < 2 * min (v i) (v j)) = c.close i j} := by
    ext v
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · intro hv
      cases hv
      exact ⟨rfl, fun _ _ => rfl⟩
    · rintro ⟨ha, hc⟩
      cases c
      simp only [configOf, Fast.Five.Config.mk.injEq]
      exact ⟨ha, funext fun i => funext fun j => hc i j⟩
  rw [h]
  refine (measurable_cfgOf (measurableSet_singleton _)).inter ?_
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases hij : i = j
  · subst j; simp
  · simpa [ne_eq, hij] using
      (measurableSet_decide_eq
        (measurableSet_lt (show Measurable (fun v : Fin n → ℝ => max (v i) (v j)) by fun_prop)
          (show Measurable (fun v : Fin n → ℝ => 2 * min (v i) (v j)) by fun_prop)) (c.close i j))

/-- Any finite-valued recording rule on colored configurations is measurable. -/
theorem measurable_of_config {n : ℕ} {β : Type*} [MeasurableSpace β]
    (F : Config n → β) : Measurable F := fun _ _ => trivial

end BeatAvg.Five
