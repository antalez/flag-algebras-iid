import BeatAvg.Sample
import BeatAvg.Cert.Sort
import BeatAvg.Cert.CfgReal

/-!
# Certificate data built from finite tables

`mkD` turns finite tables (a flag function and a class function of configurations, a quadratic form,
multipliers) into `CertData 300 (Fin 8)`. All maps are defined through sorted tuples, so they are
symmetric by construction, and measurable.
-/

open MeasureTheory Set Function

namespace BeatAvg

/-- The threshold `θ` of four sorted roots: `θ < 4`: `a = 2 z_j - z_i - z_k`;
`θ ≥ 4`: `b = max(z_k, (z_i + z_j + z_k)/2)`. -/
noncomputable def tau (θ : Fin 8) (z : Fin 4 → ℝ) : ℝ :=
  if θ.val < 4 then 2 * z (Fast.tripJ θ.val) - z (Fast.tripI θ.val) - z (Fast.tripK θ.val)
  else max (z (Fast.tripK θ.val))
    ((z (Fast.tripI θ.val) + z (Fast.tripJ θ.val) + z (Fast.tripK θ.val)) / 2)

/-- Type 0 roots: no successful target among the four sorted roots. -/
def type0 (z : Fin 4 → ℝ) : Prop := 2 * z 3 < z 0 + z 1 + z 2

theorem measurable_tau (θ : Fin 8) : Measurable (tau θ) := by
  unfold tau
  split_ifs
  · fun_prop
  · exact (measurable_pi_apply _).max (by fun_prop)

theorem measurableSet_type0 : MeasurableSet {z : Fin 4 → ℝ | type0 z} :=
  measurableSet_lt (by fun_prop) (by fun_prop)

/-- Five points: two sorted roots followed by a sorted triple. -/
noncomputable def pts23 (p : (Fin 2 → ℝ) × (Fin 3 → ℝ)) : Fin 5 → ℝ :=
  Fin.append (sortT p.1) (sortT p.2)

/-- Five points: a root followed by four sorted points. -/
noncomputable def pts14 (p : ℝ × (Fin 4 → ℝ)) : Fin 5 → ℝ := Fin.cons p.1 (sortT p.2)

theorem measurable_pts23 : Measurable pts23 := by
  refine Measurable.of_eval fun i => ?_
  refine Fin.addCases (m := 2) (n := 3)
    (motive := fun i => Measurable fun p : (Fin 2 → ℝ) × (Fin 3 → ℝ) => pts23 p i)
    (fun j => ?_) (fun j => ?_) i
  · have : Measurable fun p : (Fin 2 → ℝ) × (Fin 3 → ℝ) => sortT p.1 j :=
      (measurable_pi_apply j).comp (measurable_sortT.comp measurable_fst)
    simpa [pts23] using this
  · have : Measurable fun p : (Fin 2 → ℝ) × (Fin 3 → ℝ) => sortT p.2 j :=
      (measurable_pi_apply j).comp (measurable_sortT.comp measurable_snd)
    simpa [pts23] using this

theorem measurable_pts14 : Measurable pts14 := by
  refine Measurable.of_eval fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [pts14] using (measurable_fst : Measurable fun p : ℝ × (Fin 4 → ℝ) => p.1)
  · have : Measurable fun p : ℝ × (Fin 4 → ℝ) => sortT p.2 j :=
      (measurable_pi_apply j).comp (measurable_sortT.comp measurable_snd)
    simpa [pts14] using this

open Classical in
/-- Certificate data from finite tables. -/
noncomputable def mkD (Fflag Fcls : Fast.Cfg 5 → ℕ) (Qf : ℕ → ℕ → ℝ) (lo hi : ℕ → ℝ)
    (w1 w2 : ℕ → ℝ) (clo : ℝ) : CertData 300 (Fin 8) where
  flag p := ⟨Fflag (cfgOf (pts23 p)) % 300, Nat.mod_lt _ (by norm_num)⟩
  Q i j := Qf i.val j.val
  alo p := lo (Fcls (cfgOf (pts14 p)))
  ahi p := hi (Fcls (cfgOf (pts14 p)))
  τ θ ρ := tau θ (sortT ρ)
  u1 θ ρ := if type0 (sortT ρ) then w1 θ.val else 0
  u2 θ ρ := if type0 (sortT ρ) then w2 θ.val else 0
  clo := clo

theorem mkD_valid (Fflag Fcls : Fast.Cfg 5 → ℕ) (Qf : ℕ → ℕ → ℝ) (lo hi : ℕ → ℝ)
    (w1 w2 : ℕ → ℝ) (clo : ℝ) (B : ℝ)
    (hQ : ∀ v : Fin 300 → ℝ, 0 ≤ ∑ i, ∑ j, v i * Qf i.val j.val * v j)
    (hlo : ∀ c, 0 ≤ lo c ∧ lo c ≤ B) (hhi : ∀ c, 0 ≤ hi c ∧ hi c ≤ B)
    (hw1 : ∀ θ, 0 ≤ w1 θ ∧ w1 θ ≤ B) (hw2 : ∀ θ, 0 ≤ w2 θ ∧ w2 θ ≤ B) :
    (mkD Fflag Fcls Qf lo hi w1 w2 clo).Valid B := by
  classical
  have hB : 0 ≤ B := (hlo 0).1.trans (hlo 0).2
  have hc23 : Measurable fun p : (Fin 2 → ℝ) × (Fin 3 → ℝ) => cfgOf (pts23 p) :=
    measurable_cfgOf.comp measurable_pts23
  have hc14 : Measurable fun p : ℝ × (Fin 4 → ℝ) => cfgOf (pts14 p) :=
    measurable_cfgOf.comp measurable_pts14
  have hty : MeasurableSet {ρ : Fin 4 → ℝ | type0 (sortT ρ)} :=
    measurable_sortT measurableSet_type0
  refine
    { flag_meas := ?_, Q_psd := hQ, alo_meas := ?_, ahi_meas := ?_, τ_meas := ?_, u1_meas := ?_,
      u2_meas := ?_, alo_nonneg := fun p => (hlo _).1, alo_le := fun p => (hlo _).2,
      ahi_nonneg := fun p => (hhi _).1, ahi_le := fun p => (hhi _).2, u1_nonneg := ?_,
      u1_le := ?_, u2_nonneg := ?_, u2_le := ?_ }
  · exact (measurable_of_cfg fun c : Fast.Cfg 5 =>
      (⟨Fflag c % 300, Nat.mod_lt _ (by norm_num)⟩ : Fin 300)).comp hc23
  · exact (measurable_of_cfg fun c : Fast.Cfg 5 => lo (Fcls c)).comp hc14
  · exact (measurable_of_cfg fun c : Fast.Cfg 5 => hi (Fcls c)).comp hc14
  · intro θ; exact (measurable_tau θ).comp measurable_sortT
  · intro θ; exact Measurable.ite hty measurable_const measurable_const
  · intro θ; exact Measurable.ite hty measurable_const measurable_const
  · intro θ ρ; simp only [mkD]; split_ifs; exacts [(hw1 _).1, le_rfl]
  · intro θ ρ; simp only [mkD]; split_ifs; exacts [(hw1 _).2, hB]
  · intro θ ρ; simp only [mkD]; split_ifs; exacts [(hw2 _).1, le_rfl]
  · intro θ ρ; simp only [mkD]; split_ifs; exacts [(hw2 _).2, hB]

end BeatAvg
