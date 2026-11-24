import BeatAvg.Cert.DegTerm

/-!
# Invariance of the degree part, and the square part
-/

open MeasureTheory Set Function

namespace BeatAvg

/-- Same root, flag points up to a permutation, same third point, first two points up to a swap. -/
def RelDeg (ρ ρ' : Fin 8 → Fin 8) : Prop :=
  ρ (bZ 0) = ρ' (bZ 0) ∧ (∃ a : Equiv.Perm (Fin 4), ∀ i, ρ (bS i) = ρ' (bS (a i))) ∧
    ρ (bW 2) = ρ' (bW 2) ∧
    ∃ b : Equiv.Perm (Fin 2), ∀ i : Fin 2, ρ (bW i.castSucc) = ρ' (bW (b i).castSucc)

instance (ρ ρ' : Fin 8 → Fin 8) : Decidable (RelDeg ρ ρ') := by unfold RelDeg; infer_instance

theorem degPart_congr (T : Tab) (ω : Fin 8 → ℝ) {ρ ρ' : Fin 8 → Fin 8} (h : RelDeg ρ ρ') (x : ℝ) :
    degPart T x (ω ∘ ρ) = degPart T x (ω ∘ ρ') := by
  obtain ⟨h0, ⟨a, ha⟩, h2, b, hb⟩ := h
  have hz : (ω ∘ ρ) (bZ 0) = (ω ∘ ρ') (bZ 0) := by simp only [comp_apply]; rw [h0]
  have hS : sortT ((ω ∘ ρ) ∘ bS) = sortT ((ω ∘ ρ') ∘ bS) := by
    have : (ω ∘ ρ) ∘ bS = ((ω ∘ ρ') ∘ bS) ∘ a := by
      funext i; simp only [comp_apply]; rw [ha]
    rw [this, sortT_comp_perm]
  have hp : pts14 ((ω ∘ ρ) (bZ 0), (ω ∘ ρ) ∘ bS) = pts14 ((ω ∘ ρ') (bZ 0), (ω ∘ ρ') ∘ bS) := by
    unfold pts14; simp only [hz, hS]
  have hw2 : ((ω ∘ ρ) ∘ bW) 2 = ((ω ∘ ρ') ∘ bW) 2 := by simp only [comp_apply]; rw [h2]
  have hw01 : ((ω ∘ ρ) ∘ bW) 0 + ((ω ∘ ρ) ∘ bW) 1 = ((ω ∘ ρ') ∘ bW) 0 + ((ω ∘ ρ') ∘ bW) 1 := by
    have h1 : ∑ i : Fin 2, ((ω ∘ ρ) ∘ bW) i.castSucc = ∑ i : Fin 2, ((ω ∘ ρ') ∘ bW) i.castSucc := by
      rw [← Equiv.sum_comp b (fun i => ((ω ∘ ρ') ∘ bW) i.castSucc)]
      exact Finset.sum_congr rfl fun i _ => by simp only [comp_apply]; rw [hb]
    simpa [Fin.sum_univ_two] using h1
  have hs4 : s4 ((ω ∘ ρ) (bZ 0)) ((ω ∘ ρ) ∘ bW) = s4 ((ω ∘ ρ') (bZ 0)) ((ω ∘ ρ') ∘ bW) := by
    rw [s4_formula, s4_formula, hw01, hw2, hz]
  have hlo : T.D.alo ((ω ∘ ρ) (bZ 0), (ω ∘ ρ) ∘ bS) = T.D.alo ((ω ∘ ρ') (bZ 0), (ω ∘ ρ') ∘ bS) := by
    show T.lo (T.Fcls (cfgOf (pts14 _))) = T.lo (T.Fcls (cfgOf (pts14 _)))
    rw [hp]
  have hhi : T.D.ahi ((ω ∘ ρ) (bZ 0), (ω ∘ ρ) ∘ bS) = T.D.ahi ((ω ∘ ρ') (bZ 0), (ω ∘ ρ') ∘ bS) := by
    show T.hi (T.Fcls (cfgOf (pts14 _))) = T.hi (T.Fcls (cfgOf (pts14 _)))
    rw [hp]
  unfold degPart
  rw [split3_e143, split3_e143]
  simp only [degLoK, degHiK]
  change T.D.alo ((ω ∘ ρ) (bZ 0), (ω ∘ ρ) ∘ bS)
      * (s4 ((ω ∘ ρ) (bZ 0)) ((ω ∘ ρ) ∘ bW) / 4 - T.D.clo)
    + T.D.ahi ((ω ∘ ρ) (bZ 0), (ω ∘ ρ) ∘ bS)
      * (x - s4 ((ω ∘ ρ) (bZ 0)) ((ω ∘ ρ) ∘ bW) / 4)
    = T.D.alo ((ω ∘ ρ') (bZ 0), (ω ∘ ρ') ∘ bS)
      * (s4 ((ω ∘ ρ') (bZ 0)) ((ω ∘ ρ') ∘ bW) / 4 - T.D.clo)
    + T.D.ahi ((ω ∘ ρ') (bZ 0), (ω ∘ ρ') ∘ bS)
      * (x - s4 ((ω ∘ ρ') (bZ 0)) ((ω ∘ ρ') ∘ bW) / 4)
  rw [hlo, hhi, hs4]

/-- The square part of `lam`. -/
noncomputable def sqPart (T : Tab) (v : Fin 8 → ℝ) : ℝ := sqK T.D (split3 e233 v)

/-- The square part, evaluated from a configuration. -/
noncomputable def sqR (T : Tab) (c : Fast.Cfg 8) (ρ : Fin 8 → Fin 8) : ℝ :=
  T.Qf (T.Fflag (c.comap (ρ ∘ Fast.first5)) % 300) (T.Fflag (c.comap (ρ ∘ Fast.sel2)) % 300)

theorem sqK_tab (T : Tab) (r : Fin 2 → ℝ) (t t' : Fin 3 → ℝ) :
    sqK T.D (r, (t, t')) = T.Qf (T.Fflag (cfgOf (pts23 (r, t))) % 300)
      (T.Fflag (cfgOf (pts23 (r, t'))) % 300) := rfl

/-- Roots and both triples up to permutations. -/
def RelSq (ρ ρ' : Fin 8 → Fin 8) : Prop :=
  (∃ a : Equiv.Perm (Fin 2), ∀ i, ρ (bR i) = ρ' (bR (a i))) ∧
    (∃ b : Equiv.Perm (Fin 3), ∀ i, ρ (bT i) = ρ' (bT (b i))) ∧
    ∃ c : Equiv.Perm (Fin 3), ∀ i, ρ (bT' i) = ρ' (bT' (c i))

instance (ρ ρ' : Fin 8 → Fin 8) : Decidable (RelSq ρ ρ') := by unfold RelSq; infer_instance

theorem sqPart_congr (T : Tab) (ω : Fin 8 → ℝ) {ρ ρ' : Fin 8 → Fin 8} (h : RelSq ρ ρ') :
    sqPart T (ω ∘ ρ) = sqPart T (ω ∘ ρ') := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, c, hc⟩ := h
  have hR : sortT ((ω ∘ ρ) ∘ bR) = sortT ((ω ∘ ρ') ∘ bR) := by
    have : (ω ∘ ρ) ∘ bR = ((ω ∘ ρ') ∘ bR) ∘ a := by
      funext i; simp only [comp_apply]; rw [ha]
    rw [this, sortT_comp_perm]
  have hT : sortT ((ω ∘ ρ) ∘ bT) = sortT ((ω ∘ ρ') ∘ bT) := by
    have : (ω ∘ ρ) ∘ bT = ((ω ∘ ρ') ∘ bT) ∘ b := by
      funext i; simp only [comp_apply]; rw [hb]
    rw [this, sortT_comp_perm]
  have hT' : sortT ((ω ∘ ρ) ∘ bT') = sortT ((ω ∘ ρ') ∘ bT') := by
    have : (ω ∘ ρ) ∘ bT' = ((ω ∘ ρ') ∘ bT') ∘ c := by
      funext i; simp only [comp_apply]; rw [hc]
    rw [this, sortT_comp_perm]
  unfold sqPart
  rw [split3_e233, split3_e233, sqK_tab, sqK_tab]
  simp only [pts23, hR, hT, hT']

end BeatAvg
