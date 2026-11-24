import BeatAvg.ExpectDeg
import BeatAvg.Atomless

/-!
# Theorem D and the two-point criterion, in sample form

`C_le_of_certificate`: if certificate data `D` is valid, `c_lo ≤ X`, and the symmetrised functional
satisfies `Λ(ω, X) ≤ X` and `Λ(ω, Cbar0) ≤ Cbar0 - δ` for every eight-point sample `ω` in general
position, and `C ≤ Cbar0`, then `C ≤ X`.

The lower bound `c_lo ≤ C` of `theorem_D_proof.md` is not a hypothesis: if `C < X` there is nothing
to prove, and otherwise `c_lo ≤ X ≤ C`.
-/

open MeasureTheory Set Function

namespace BeatAvg

variable {nΦ : ℕ} {Θ : Type} [Fintype Θ] {D : CertData nΦ Θ} {B : ℝ}

theorem bm_lam (hD : D.Valid B) (x : ℝ) : BM (lam D x) := by
  have hm3a : Measurable (split3 (X := ℝ) e233) := by unfold split3; fun_prop
  have hm3b : Measurable (split3 (X := ℝ) e143) := by unfold split3; fun_prop
  show BM fun ω => objT ω + sqK D (split3 e233 ω) + degLoK D (split3 e143 ω)
    + degHiK D x (split3 e143 ω)
    + ∑ θ, (thr1K D θ x (split e44 ω) + thr2K D θ (split e44 ω))
  exact ((((bm_objT.add ((bm_sqK hD).comp hm3a)).add ((bm_degLoK hD).comp hm3b)).add
    ((bm_degHiK hD x).comp hm3b)).add (BM.sum _ fun θ _ =>
      ((bm_thr1K hD θ x).comp (measurable_split e44)).add
        ((bm_thr2K hD θ).comp (measurable_split e44))))

theorem measurable_comp_perm (π : Equiv.Perm (Fin 8)) :
    Measurable fun ω : Fin 8 → ℝ => ω ∘ π :=
  Measurable.of_eval fun k => measurable_pi_apply (π k)

theorem bm_Lam (hD : D.Valid B) (x : ℝ) : BM (Lam D x) := by
  show BM fun ω => (1 / (Nat.factorial 8 : ℝ)) * ∑ π : Equiv.Perm (Fin 8), lam D x (ω ∘ π)
  exact (BM.sum _ fun π _ => (bm_lam hD x).comp (measurable_comp_perm π)).const_mul _

/-- Exchangeability: the symmetrised functional has the same mean as `lam`. -/
theorem integral_Lam (hD : D.Valid B) (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    ∫ ω, Lam D x ω ∂(iid 8 μ) = ∫ ω, lam D x ω ∂(iid 8 μ) := by
  have hint : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin 8))),
      Integrable (fun ω : Fin 8 → ℝ => lam D x (ω ∘ π)) (iid 8 μ) := fun π _ =>
    ((bm_lam hD x).comp (measurable_comp_perm π)).integrable _
  have hperm : ∀ π : Equiv.Perm (Fin 8),
      ∫ ω : Fin 8 → ℝ, lam D x (ω ∘ π) ∂(iid 8 μ) = ∫ ω, lam D x ω ∂(iid 8 μ) := fun π =>
    integral_comp_mp (measurePreserving_comp_injective (ι := Fin 8) μ π π.injective)
      (bm_lam hD x).meas
  simp only [Lam]
  rw [integral_const_mul, integral_finsetSum _ hint]
  simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  have : ((Nat.factorial 8 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Theorem D with the two-point criterion (sample form).** -/
theorem C_le_of_certificate (hD : D.Valid B) {X Cbar0 δ : ℝ} (hδ : 0 < δ) (hclo : D.clo ≤ X)
    (hX : ∀ ω, Generic ω → Lam D X ω ≤ X)
    (h0 : ∀ ω, Generic ω → Lam D Cbar0 ω ≤ Cbar0 - δ)
    (hC : C ≤ Cbar0) : C ≤ X := by
  by_contra hcon
  have hXC : X < C := not_le.mp hcon
  have hXC0 : X < Cbar0 := lt_of_lt_of_le hXC hC
  obtain ⟨s, hsdef⟩ : ∃ s, s = (C - X) / (Cbar0 - X) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact div_pos (sub_pos.2 hXC) (sub_pos.2 hXC0)
  have hs1 : s ≤ 1 := by
    rw [hsdef]; exact (div_le_one (sub_pos.2 hXC0)).2 (by linarith)
  have hCeq : C = (1 - s) * X + s * Cbar0 := by
    have hne : Cbar0 - X ≠ 0 := (sub_pos.2 hXC0).ne'
    rw [hsdef]
    field_simp
    ring
  -- the functional at `C` is below `C` with a margin, on samples in general position
  have hgen : ∀ ω, Generic ω → Lam D C ω ≤ C - s * δ := by
    intro ω hω
    have hconv := Lam_convex D X Cbar0 s ω
    rw [← hCeq] at hconv
    rw [hconv]
    have h1 := mul_le_mul_of_nonneg_left (hX ω hω) (sub_nonneg.2 hs1)
    have h2 := mul_le_mul_of_nonneg_left (h0 ω hω) hs0.le
    nlinarith
  have hB0 : 0 ≤ B := (hD.alo_nonneg (0, 0)).trans (hD.alo_le (0, 0))
  have hcard : (0 : ℝ) ≤ (Fintype.card Θ : ℝ) := Nat.cast_nonneg _
  -- choice of `ε = t ^ 2`
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + 16 * B + 2 * (Fintype.card Θ : ℝ) * B := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    have := mul_nonneg hcard hB0
    linarith
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = min (1 / 6) (s * δ / (2 * K)) := ⟨_, rfl⟩
  have hsδ : 0 < s * δ := mul_pos hs0 hδ
  have ht0 : 0 < t := by
    rw [htdef]
    exact lt_min (by norm_num) (div_pos hsδ (by linarith))
  have ht6 : t ≤ 1 / 6 := by rw [htdef]; exact min_le_left _ _
  have htK : t * (2 * K) ≤ s * δ := by
    have : t ≤ s * δ / (2 * K) := by rw [htdef]; exact min_le_right _ _
    exact (le_div_iff₀ (by linarith)).1 this
  have hε0 : 0 < t ^ 2 := by positivity
  have hε : t ^ 2 ≤ 1 / 36 := by nlinarith
  have hsqrt : Real.sqrt (t ^ 2) = t := Real.sqrt_sq ht0.le
  obtain ⟨ν, hν, hna, hP⟩ := exists_atomless_law_gt hε0
  have := hν.prob
  have hge := integral_lam_ge hD hν hε0 hε hP.le (hclo.trans hXC.le)
  rw [hsqrt] at hge
  have hle : ∫ ω, Lam D C ω ∂(iid 8 ν) ≤ C - s * δ := by
    have h := integral_mono_ae ((bm_Lam hD C).integrable (iid 8 ν)) (integrable_const (C - s * δ))
      ((ae_generic hν).mono fun ω hω => hgen ω hω)
    simpa using h
  rw [integral_Lam hD ν C] at hle
  -- arithmetic: s δ ≤ ε + 16 B t + 2 |Θ| ε B ≤ t K ≤ s δ / 2
  have hεt : t ^ 2 ≤ t := by nlinarith
  have h1 : (Fintype.card Θ : ℝ) * (2 * t ^ 2 * B) ≤ (Fintype.card Θ : ℝ) * (2 * t * B) := by
    have : 2 * t ^ 2 * B ≤ 2 * t * B := by nlinarith
    exact mul_le_mul_of_nonneg_left this hcard
  have h2 : t * K = t + 16 * B * t + (Fintype.card Θ : ℝ) * (2 * t * B) := by
    rw [hKdef]; ring
  nlinarith

end BeatAvg
