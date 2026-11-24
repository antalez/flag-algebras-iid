import BeatAvg.Lower.Construct
import BeatAvg.Cert.BstarFacts

/-!
# The lower bound `B* ≤ C`

Proposition "Lower bound" of the paper: `C ≥ p (2 - p) / (1 + p + p² + p³)` for every `p ∈ (0, 1)`.

The paper iterates the construction `Y = X + η Y'` infinitely often and uses that `Y'` has the law
of `Y`. Here one step is enough: `Y'` ranges over all laws, and the supremum `C` appears on both
sides, `C ≥ p^4 C + p (1 - p) (2 - p) - O(1/N)`.
-/

open MeasureTheory

namespace BeatAvg

open Lower

/-- The supremum reproduces itself at the atom `0`: `C ≥ p^4 C + E[Ff]`. -/
theorem C_ge_step {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {N : ℕ} (hN : 0 < N) :
    p ^ 4 * C + (∫ k, Ff k ∂(Measure.pi fun _ : Fin 4 => gridM p N)) ≤ C := by
  by_contra hcon
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ∫ k, Ff k ∂(Measure.pi fun _ : Fin 4 => gridM p N) := ⟨_, rfl⟩
  rw [← ha] at hcon
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = p ^ 4 * C + a - C := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; linarith [not_le.mp hcon]
  obtain ⟨lam, hl, hlam⟩ := exists_law_gt (ε := g / 4) (by linarith)
  have hδ : 0 < min 1 (g / 16) := lt_min one_pos (by linarith)
  obtain ⟨μ, hμ, h⟩ := one_step hp0 hp1 hN hl hδ (min_le_left _ _)
  rw [← ha] at h
  have h1 := P_le_C hμ
  have h2 : min 1 (g / 16) ≤ g / 16 := min_le_right _ _
  have hp4 : p ^ 4 ≤ 1 := pow_le_one₀ hp0 hp1
  have hp40 : 0 ≤ p ^ 4 := by positivity
  have h3 : p ^ 4 * (C - g / 4) ≤ p ^ 4 * P lam := mul_le_mul_of_nonneg_left hlam.le hp40
  nlinarith

/-- **Lower bound** (Bellec–Fritz, Proposition "Lower bound"). -/
theorem lower_bound {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    p * (2 - p) / (1 + p + p ^ 2 + p ^ 3) ≤ C := by
  have key : p * (1 - p) * (2 - p) ≤ C * (1 - p ^ 4) := by
    by_contra hcon
    obtain ⟨g, hg⟩ : ∃ g : ℝ, g = p * (1 - p) * (2 - p) - C * (1 - p ^ 4) := ⟨_, rfl⟩
    have hg0 : 0 < g := by rw [hg]; linarith [not_le.mp hcon]
    obtain ⟨n, hn⟩ := exists_nat_gt (3 / g)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = n + 1 := ⟨_, rfl⟩
    have hNpos : 0 < N := by omega
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hNg : 3 / g < (N : ℝ) := by
      rw [hN]; push_cast; linarith
    have h := C_ge_step hp0.le hp1.le hNpos
    rw [int_Ff hp0.le hp1.le hNpos] at h
    -- the count of the paper: `2/3 - 1/N`
    have hc : 2 / 3 - 1 / (N : ℝ) ≤ ((N : ℝ) - 1) * (4 * N + 1) / (6 * N ^ 2) := by
      have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
      rw [div_sub_div _ _ (by norm_num) hNr.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hq : 0 ≤ 3 * p * (1 - p) ^ 3 := by
      have : 0 ≤ 1 - p := by linarith
      positivity
    have hq1 : 3 * p * (1 - p) ^ 3 ≤ 3 := by
      have h1 : (1 - p) ^ 3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have h2 : 0 ≤ (1 - p) ^ 3 := by
        have : 0 ≤ 1 - p := by linarith
        positivity
      nlinarith
    have h5 := mul_le_mul_of_nonneg_left hc hq
    have h6 : 3 / (N : ℝ) < g := by
      rw [div_lt_iff₀ hNr]
      rw [div_lt_iff₀ hg0] at hNg
      linarith
    have h7 : 3 * p * (1 - p) ^ 3 * (1 / (N : ℝ)) ≤ 3 / (N : ℝ) := by
      rw [show (3 : ℝ) / N = 3 * (1 / (N : ℝ)) by ring]
      exact mul_le_mul_of_nonneg_right hq1 (by positivity)
    nlinarith
  have hden : 0 < 1 + p + p ^ 2 + p ^ 3 := by positivity
  rw [div_le_iff₀ hden]
  have h1p : 0 < 1 - p := by linarith
  have e : C * (1 - p ^ 4) = C * (1 + p + p ^ 2 + p ^ 3) * (1 - p) := by ring
  have e2 : p * (1 - p) * (2 - p) = p * (2 - p) * (1 - p) := by ring
  rw [e, e2] at key
  exact le_of_mul_le_mul_right key h1p

/-- **The Beat the Average constant is at least `B*`.** -/
theorem Bstar_le_C : Bstar ≤ C := by
  rw [Bstar_eq]
  exact lower_bound (by linarith [rr_bounds.1]) (by linarith [rr_bounds.2])

end BeatAvg
