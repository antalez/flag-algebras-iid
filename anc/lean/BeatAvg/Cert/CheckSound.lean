import BeatAvg.Cert.EvalZ
import BeatAvg.Cert.Sorted

/-!
# Soundness of the per-pattern checks
-/

namespace BeatAvg

theorem fact8 : (Nat.factorial 8 : ℝ) = 40320 := by norm_num [Nat.factorial]

theorem checkB_sound {lo hi : ℤ} {m : ℕ} (he : Encl lo hi m) (t : Fast.Tabs) (hDn : 0 < t.Dn)
    {ω : Fin 8 → ℝ} (hω : SG8 ω) (h : Fast.checkB lo hi m t (cfgOf ω) = true) :
    Lam (tabOf t).D Bstar ω ≤ Bstar := by
  have hD : (0 : ℝ) < (t.Dn : ℝ) := by exact_mod_cast hDn
  have h1 := nonneg_sound he h
  simp only [evalZ_sub, evalZ_smul, evalZ_mul, evalZ_b4] at h1
  have h2 := lamUV_eval t (cfgOf ω) hD.ne' Bstar
  rw [Lam_sorted _ hω, fact8]
  push_cast at h1
  have h3 : (t.Dn : ℝ) * LamR (tabOf t) (cfgOf ω) Bstar ≤ (t.Dn : ℝ) * (40320 * Bstar) := by
    nlinarith
  have h4 := le_of_mul_le_mul_left h3 hD
  rw [one_div, inv_mul_le_iff₀ (by norm_num)]
  linarith

theorem checkC_sound {lo hi : ℤ} {m : ℕ} (he : Encl lo hi m) (t : Fast.Tabs) (hDn : 0 < t.Dn)
    {p q e : ℤ} (hq : 0 < q) {ω : Fin 8 → ℝ} (hω : SG8 ω)
    (h : Fast.checkC lo hi m t p q e (cfgOf ω) = true) :
    Lam (tabOf t).D ((p : ℝ) / q) ω ≤ ((p : ℝ) - e) / q := by
  have hD : (0 : ℝ) < (t.Dn : ℝ) := by exact_mod_cast hDn
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h1 := nonneg_sound he h
  simp only [evalZ_sub, evalZ_smul, evalZ_ofInt] at h1
  have h2 := lamUV_eval t (cfgOf ω) hD.ne' ((p : ℝ) / q)
  rw [Lam_sorted _ hω, fact8]
  push_cast at h1
  have h2' : (q : ℝ) * evalZ (Fast.lamU t (cfgOf ω)) + 4 * p * evalZ (Fast.lamV t (cfgOf ω))
      = q * (4 * t.Dn * LamR (tabOf t) (cfgOf ω) ((p : ℝ) / q)) := by
    rw [← h2]; field_simp
  have h3 : (4 * (t.Dn : ℝ) * q) * LamR (tabOf t) (cfgOf ω) ((p : ℝ) / q)
      ≤ (4 * (t.Dn : ℝ) * q) * (40320 * (((p : ℝ) - e) / q)) := by
    have : (4 * (t.Dn : ℝ) * q) * (40320 * (((p : ℝ) - e) / q))
        = 4 * t.Dn * 40320 * ((p : ℝ) - e) := by field_simp
    rw [this]
    nlinarith
  have h4 := le_of_mul_le_mul_left h3 (by positivity)
  rw [one_div, inv_mul_le_iff₀ (by norm_num)]
  linarith

end BeatAvg
