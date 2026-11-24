import BeatAvg.Cert.ObjTerm

/-!
# The degree part of the functional on arrangements
-/

open MeasureTheory Set Function

namespace BeatAvg

theorem ind_S4 (v : Fin 4 → ℝ) : ind S4 v = if v 0 + v 1 + v 2 < 2 * v 3 then 1 else 0 := by
  by_cases h : v 0 + v 1 + v 2 < 2 * v 3
  · rw [ind_of_mem (show v ∈ S4 from h), if_pos h]
  · rw [ind_of_notMem (show v ∉ S4 from h), if_neg h]

theorem s4_formula (x : ℝ) (w : Fin 3 → ℝ) :
    s4 x w = 3 * (if x + (w 0 + w 1) < 2 * w 2 then 1 else 0)
      + (if w 0 + w 1 + w 2 < 2 * x then 1 else 0) := by
  unfold s4
  rw [Fin.sum_univ_four]
  simp only [ind_S4]
  change (if x + w 0 + w 1 < 2 * w 2 then (1 : ℝ) else 0)
    + (if w 0 + x + w 1 < 2 * w 2 then 1 else 0) + (if w 0 + w 1 + x < 2 * w 2 then 1 else 0)
    + (if w 0 + w 1 + w 2 < 2 * x then 1 else 0) = _
  simp only [show w 0 + x + w 1 = x + (w 0 + w 1) by ring,
    show w 0 + w 1 + x = x + (w 0 + w 1) by ring, show x + w 0 + w 1 = x + (w 0 + w 1) by ring]
  ring

/-- The degree part of `lam`. -/
noncomputable def degPart (T : Tab) (x : ℝ) (v : Fin 8 → ℝ) : ℝ :=
  degLoK T.D (split3 e143 v) + degHiK T.D x (split3 e143 v)

/-- The degree part, evaluated from a configuration. -/
noncomputable def degR (T : Tab) (c : Fast.Cfg 8) (ρ : Fin 8 → Fin 8) (x : ℝ) : ℝ :=
  T.lo (T.Fcls (c.comap (ρ ∘ Fast.first5))) * ((Fast.s4C c ρ : ℝ) / 4 - T.clo)
    + T.hi (T.Fcls (c.comap (ρ ∘ Fast.first5))) * (x - (Fast.s4C c ρ : ℝ) / 4)

theorem first5_injective : Injective Fast.first5 := Fin.castAdd_injective 5 3

theorem s4C_eval (ω : Fin 8 → ℝ) {ρ : Fin 8 → Fin 8} (hρ : Injective ρ) :
    s4 ((ω ∘ ρ) (bZ 0)) ((ω ∘ ρ) ∘ bW) = (Fast.s4C (cfgOf ω) ρ : ℝ) := by
  rw [s4_formula]
  have h1 := sb_cfgOf ω (a := ρ 0) (b := ρ 5) (c := ρ 6) (d := ρ 7) (hρ.ne (by decide))
    (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide))
    (hρ.ne (by decide))
  have h2 := sb_cfgOf ω (a := ρ 5) (b := ρ 6) (c := ρ 7) (d := ρ 0) (hρ.ne (by decide))
    (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide))
    (hρ.ne (by decide))
  change 3 * (if ω (ρ 0) + (ω (ρ 5) + ω (ρ 6)) < 2 * ω (ρ 7) then (1 : ℝ) else 0)
    + (if ω (ρ 5) + ω (ρ 6) + ω (ρ 7) < 2 * ω (ρ 0) then 1 else 0) = _
  unfold Fast.s4C
  by_cases c1 : (cfgOf ω).sb (ρ 0) (ρ 5) (ρ 6) (ρ 7) = true <;>
    by_cases c2 : (cfgOf ω).sb (ρ 5) (ρ 6) (ρ 7) (ρ 0) = true
  · have e1 : ω (ρ 0) + (ω (ρ 5) + ω (ρ 6)) < 2 * ω (ρ 7) := by have := h1.1 c1; linarith
    simp [c1, c2, e1, h2.1 c2]
    norm_num
  · have e1 : ω (ρ 0) + (ω (ρ 5) + ω (ρ 6)) < 2 * ω (ρ 7) := by have := h1.1 c1; linarith
    have e2 : ¬ (ω (ρ 5) + ω (ρ 6) + ω (ρ 7) < 2 * ω (ρ 0)) := fun h => c2 (h2.2 h)
    simp [c1, c2, e1, e2]
  · have e1 : ¬ (ω (ρ 0) + (ω (ρ 5) + ω (ρ 6)) < 2 * ω (ρ 7)) :=
      fun h => c1 (h1.2 (by linarith))
    simp [c1, c2, e1, h2.1 c2]
  · have e1 : ¬ (ω (ρ 0) + (ω (ρ 5) + ω (ρ 6)) < 2 * ω (ρ 7)) :=
      fun h => c1 (h1.2 (by linarith))
    have e2 : ¬ (ω (ρ 5) + ω (ρ 6) + ω (ρ 7) < 2 * ω (ρ 0)) := fun h => c2 (h2.2 h)
    simp [c1, c2, e1, e2]

theorem pts14_eval {ω : Fin 8 → ℝ} (hω : SG8 ω) {ρ : Fin 8 → Fin 8} (hmono : Monotone (ρ ∘ bS)) :
    pts14 ((ω ∘ ρ) (bZ 0), (ω ∘ ρ) ∘ bS) = ω ∘ (ρ ∘ Fast.first5) := by
  have hsort : sortT ((ω ∘ ρ) ∘ bS) = (ω ∘ ρ) ∘ bS :=
    sortT_of_monotone (hω.mono.monotone.comp hmono)
  unfold pts14
  simp only [hsort]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rw [Fin.cons_succ]
    show ω (ρ (bS j)) = ω (ρ (Fast.first5 j.succ))
    have : bS j = Fast.first5 j.succ := by
      apply Fin.ext
      simp only [bS_val, Fast.first5, Fin.val_castAdd, Fin.val_succ]
      omega
    rw [this]

theorem degPart_eval (T : Tab) {ω : Fin 8 → ℝ} (hω : SG8 ω) {ρ : Fin 8 → Fin 8} (hρ : Injective ρ)
    (hmono : Monotone (ρ ∘ bS)) (x : ℝ) :
    degPart T x (ω ∘ ρ) = degR T (cfgOf ω) ρ x := by
  have hc : cfgOf (pts14 ((ω ∘ ρ) (bZ 0), (ω ∘ ρ) ∘ bS)) = (cfgOf ω).comap (ρ ∘ Fast.first5) := by
    rw [pts14_eval hω hmono, cfgOf_comp ω _ (hρ.comp first5_injective)]
  have hlo : T.D.alo ((ω ∘ ρ) (bZ 0), (ω ∘ ρ) ∘ bS)
      = T.lo (T.Fcls ((cfgOf ω).comap (ρ ∘ Fast.first5))) := by
    show T.lo (T.Fcls (cfgOf (pts14 _))) = _
    rw [hc]
  have hhi : T.D.ahi ((ω ∘ ρ) (bZ 0), (ω ∘ ρ) ∘ bS)
      = T.hi (T.Fcls ((cfgOf ω).comap (ρ ∘ Fast.first5))) := by
    show T.hi (T.Fcls (cfgOf (pts14 _))) = _
    rw [hc]
  unfold degPart degR
  rw [split3_e143]
  simp only [degLoK, degHiK]
  change T.D.alo ((ω ∘ ρ) (bZ 0), (ω ∘ ρ) ∘ bS)
      * (s4 ((ω ∘ ρ) (bZ 0)) ((ω ∘ ρ) ∘ bW) / 4 - T.D.clo)
    + T.D.ahi ((ω ∘ ρ) (bZ 0), (ω ∘ ρ) ∘ bS)
      * (x - s4 ((ω ∘ ρ) (bZ 0)) ((ω ∘ ρ) ∘ bW) / 4) = _
  rw [hlo, hhi, s4C_eval ω hρ]
  rfl

end BeatAvg
