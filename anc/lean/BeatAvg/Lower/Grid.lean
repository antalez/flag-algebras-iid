import BeatAvg.Bounded
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The discrete law of the lower bound, on its index set

The paper takes `ν = p δ_0 + (1 - p)/N ∑_{i=1}^N δ_{1 - 2^{-i}}`. Here the atoms are indexed by
`Fin (N + 1)`: index `0` is the atom at `0`, index `i ≥ 1` is the atom at `1 - 2^{-i}`. This file
defines the law of the index and computes integrals against it and against its fourth power.
-/

open MeasureTheory Finset
open scoped NNReal

namespace BeatAvg.Lower

/-- Weight of the atom with index `j`. -/
noncomputable def wt (p : ℝ) (N : ℕ) (j : Fin (N + 1)) : ℝ :=
  if (j : ℕ) = 0 then p else (1 - p) / N

/-- The law of the index. -/
noncomputable def gridM (p : ℝ) (N : ℕ) : Measure (Fin (N + 1)) :=
  ∑ j, (wt p N j).toNNReal • Measure.dirac j

variable {p : ℝ} {N : ℕ}

theorem wt_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j : Fin (N + 1)) : 0 ≤ wt p N j := by
  unfold wt
  split_ifs
  · exact hp0
  · exact div_nonneg (by linarith) (Nat.cast_nonneg N)

instance : IsFiniteMeasure (gridM p N) := by
  unfold gridM
  infer_instance

/-- Integral against the law of the index. -/
theorem integral_gridM (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : Fin (N + 1) → ℝ) :
    ∫ j, g j ∂(gridM p N) = p * g 0 + (1 - p) / N * ∑ i : Fin N, g i.succ := by
  unfold gridM
  rw [integral_finsetSum_measure (fun j _ => Integrable.of_finite)]
  simp only [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (wt_nonneg hp0 hp1 _)]
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  simp [wt]

theorem gridM_prob (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : 0 < N) : IsProbabilityMeasure (gridM p N) := by
  have h := integral_gridM (N := N) hp0 hp1 (fun _ => (1 : ℝ))
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [integral_const, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  rw [div_mul_cancel₀ _ hN'] at h
  have h1 : (gridM p N).real Set.univ = 1 := by linarith
  refine ⟨?_⟩
  have := (ENNReal.toReal_eq_one_iff _).1 h1
  exact this

/-- Integral of a product of functions of the four coordinates. -/
theorem int4 (m : Measure (Fin (N + 1))) [IsProbabilityMeasure m] (f0 f1 f2 f3 : Fin (N + 1) → ℝ) :
    ∫ k : Fin 4 → Fin (N + 1), f0 (k 0) * f1 (k 1) * f2 (k 2) * f3 (k 3)
        ∂(Measure.pi fun _ : Fin 4 => m)
      = (∫ j, f0 j ∂m) * (∫ j, f1 j ∂m) * (∫ j, f2 j ∂m) * (∫ j, f3 j ∂m) := by
  have h := integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun _ : Fin 4 => m)
    (fun i : Fin 4 => (![f0, f1, f2, f3] i : Fin (N + 1) → ℝ))
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] at h
  simpa using h

/-! ### Indicator functions of the index -/

/-- The atom at zero. -/
def zf (j : Fin (N + 1)) : ℝ := if (j : ℕ) = 0 then 1 else 0
/-- The positive atoms. -/
def nf (j : Fin (N + 1)) : ℝ := if (j : ℕ) = 0 then 0 else 1
/-- The atom with index `t + 1`. -/
def ef (t : ℕ) (j : Fin (N + 1)) : ℝ := if (j : ℕ) = t + 1 then 1 else 0
/-- The positive atoms with index at most `t`. -/
def Lf (t : ℕ) (j : Fin (N + 1)) : ℝ := if 0 < (j : ℕ) ∧ (j : ℕ) ≤ t then 1 else 0
/-- The atoms with index at least `t + 1`. -/
def Uf (t : ℕ) (j : Fin (N + 1)) : ℝ := if t + 1 ≤ (j : ℕ) then 1 else 0

theorem sum_fin_ite (N : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    ∑ i : Fin N, (if q (i : ℕ) then (1 : ℝ) else 0) = ((Finset.range N).filter q).card := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if q i then (1 : ℝ) else 0) N, Finset.sum_boole]

theorem int_zf (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ∫ j, zf j ∂(gridM p N) = p := by
  rw [integral_gridM hp0 hp1]
  simp [zf]

theorem int_nf (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : 0 < N) : ∫ j, nf j ∂(gridM p N) = 1 - p := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [integral_gridM hp0 hp1]
  simp [nf, div_mul_cancel₀ _ hN']

theorem int_ef (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {t : ℕ} (ht : t < N) :
    ∫ j, ef t j ∂(gridM p N) = (1 - p) / N := by
  rw [integral_gridM hp0 hp1]
  have h : ∑ i : Fin N, ef t (i.succ : Fin (N + 1)) = 1 := by
    have e : ∀ i : Fin N, ef t (i.succ : Fin (N + 1)) = if (i : ℕ) = t then 1 else 0 := by
      intro i; simp [ef]
    simp only [e]
    rw [sum_fin_ite N (fun i => i = t)]
    have : (Finset.range N).filter (fun i => i = t) = {t} := by
      ext i; simp only [mem_filter, mem_range, mem_singleton]; omega
    rw [this]; simp
  rw [h]
  simp [ef]

theorem int_Lf (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {t : ℕ} (ht : t ≤ N) :
    ∫ j, Lf t j ∂(gridM p N) = (1 - p) / N * t := by
  rw [integral_gridM hp0 hp1]
  have h : ∑ i : Fin N, Lf t (i.succ : Fin (N + 1)) = t := by
    have e : ∀ i : Fin N, Lf t (i.succ : Fin (N + 1)) = if (i : ℕ) < t then 1 else 0 := by
      intro i; simp [Lf]
    simp only [e]
    rw [sum_fin_ite N (fun i => i < t)]
    have : (Finset.range N).filter (fun i => i < t) = Finset.range t := by
      ext i; simp only [mem_filter, mem_range]; omega
    rw [this]; simp
  rw [h]
  simp [Lf]

theorem int_Uf (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {t : ℕ} (ht : t ≤ N) :
    ∫ j, Uf t j ∂(gridM p N) = (1 - p) / N * ((N : ℝ) - t) := by
  rw [integral_gridM hp0 hp1]
  have h : ∑ i : Fin N, Uf t (i.succ : Fin (N + 1)) = (N : ℝ) - t := by
    have e : ∀ i : Fin N, Uf t (i.succ : Fin (N + 1)) = if t ≤ (i : ℕ) then 1 else 0 := by
      intro i; simp [Uf]
    simp only [e]
    rw [sum_fin_ite N (fun i => t ≤ i)]
    have : (Finset.range N).filter (fun i => t ≤ i) = Finset.Ico t N := by
      ext i; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [this, Nat.card_Ico, Nat.cast_sub ht]
  rw [h]
  simp [Uf]

end BeatAvg.Lower
