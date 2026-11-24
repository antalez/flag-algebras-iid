import BeatAvg.Lower.Grid

/-!
# The events of the paper's lower bound, on the index set

With `X_i` the atom of index `k i`, the paper bounds `P(X_1 + X_2 + X_3 < 2 X_4)` from below by the
probabilities of three kinds of events: three summands at `0`; two summands at `0`; one summand at
`0` and another one below the target. `Ff` is the sum of the indicators of these events, written
as products of functions of single coordinates so that its mean is a product of one-dimensional
integrals. On these events the inequality holds with the margin `2^{-N}` (`Gap`).
-/

open MeasureTheory Finset

namespace BeatAvg.Lower

variable {p : ℝ} {N : ℕ}

/-- The atom with index `j`: `1 - 2^{-j}`. -/
noncomputable def val (j : Fin (N + 1)) : ℝ := 1 - (1 / 2 : ℝ) ^ (j : ℕ)

/-- The strict inequality with margin `2^{-N}`. -/
def Gap (k : Fin 4 → Fin (N + 1)) : Prop :=
  val (k 0) + val (k 1) + val (k 2) + (1 / 2 : ℝ) ^ N ≤ 2 * val (k 3)

/-- One summand at `0`, one summand below the target of index `t + 1`. -/
noncomputable def Hf (t : ℕ) (k : Fin 4 → Fin (N + 1)) : ℝ :=
  zf (k 0) * Lf t (k 1) * nf (k 2) + zf (k 0) * Uf t (k 1) * Lf t (k 2)
    + Lf t (k 0) * zf (k 1) * nf (k 2) + Uf t (k 0) * zf (k 1) * Lf t (k 2)
    + Lf t (k 0) * nf (k 1) * zf (k 2) + Uf t (k 0) * Lf t (k 1) * zf (k 2)

/-- Sum of the indicators of the events of the lower bound. -/
noncomputable def Ff (k : Fin 4 → Fin (N + 1)) : ℝ :=
  zf (k 0) * zf (k 1) * zf (k 2) * nf (k 3) + zf (k 0) * zf (k 1) * nf (k 2) * nf (k 3)
    + zf (k 0) * nf (k 1) * zf (k 2) * nf (k 3) + nf (k 0) * zf (k 1) * zf (k 2) * nf (k 3)
    + ∑ t ∈ range N, Hf t k * ef t (k 3)

/-! ### Values of the atoms -/

theorem val_zero {j : Fin (N + 1)} (h : (j : ℕ) = 0) : val j = 0 := by simp [val, h]

/-- Every atom is at most `1 - 2^{-N}`. -/
theorem val_add_le (j : Fin (N + 1)) : val j + (1 / 2 : ℝ) ^ N ≤ 1 := by
  have h : (1 / 2 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ (j : ℕ) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.lt_succ_iff.1 j.isLt)
  unfold val; linarith

/-- An atom below the atom `x` is at most `2 x - 1`. -/
theorem one_add_val_le {i j : Fin (N + 1)} (h : (i : ℕ) < (j : ℕ)) : 1 + val i ≤ 2 * val j := by
  have h1 : (1 / 2 : ℝ) ^ (j : ℕ) ≤ (1 / 2 : ℝ) ^ ((i : ℕ) + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  rw [pow_succ] at h1
  unfold val; linarith

theorem val_nonneg (j : Fin (N + 1)) : 0 ≤ val j := by
  have : (1 / 2 : ℝ) ^ (j : ℕ) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold val; linarith

/-- A positive atom is at least `1/2`. -/
theorem one_le_two_val {j : Fin (N + 1)} (h : 0 < (j : ℕ)) : 1 ≤ 2 * val j := by
  have h1 : (1 / 2 : ℝ) ^ (j : ℕ) ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  unfold val; linarith

/-! ### The events imply the inequality with margin -/

theorem sum_ef (j : Fin (N + 1)) (X : ℕ → ℝ) :
    ∑ t ∈ range N, X t * ef t j = if 0 < (j : ℕ) then X ((j : ℕ) - 1) else 0 := by
  have hj : (j : ℕ) ≤ N := Nat.lt_succ_iff.1 j.isLt
  by_cases h : 0 < (j : ℕ)
  · rw [if_pos h, Finset.sum_eq_single ((j : ℕ) - 1)]
    · have : (j : ℕ) = (j : ℕ) - 1 + 1 := by omega
      simp [ef, ← this]
    · intro t _ ht
      have : (j : ℕ) ≠ t + 1 := by omega
      simp [ef, this]
    · intro hn
      exact absurd (mem_range.2 (by omega)) hn
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun t _ => ?_
    have : (j : ℕ) ≠ t + 1 := by omega
    simp [ef, this]

theorem Lf_pred {i j : Fin (N + 1)} (hj : 0 < (j : ℕ)) :
    Lf ((j : ℕ) - 1) i = if 0 < (i : ℕ) ∧ (i : ℕ) < (j : ℕ) then 1 else 0 := by
  unfold Lf
  refine if_congr ?_ rfl rfl
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem Uf_pred {i j : Fin (N + 1)} (hj : 0 < (j : ℕ)) :
    Uf ((j : ℕ) - 1) i = if (j : ℕ) ≤ (i : ℕ) then 1 else 0 := by
  unfold Uf
  refine if_congr ?_ rfl rfl
  constructor <;> intro h <;> omega

open Classical in
/-- `Ff` is at most the indicator of the inequality with margin. -/
theorem Ff_le (k : Fin 4 → Fin (N + 1)) : Ff k ≤ if Gap k then 1 else 0 := by
  have hpow : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N := by positivity
  have hpow1 : (1 / 2 : ℝ) ^ N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold Ff
  rw [sum_ef]
  rcases Nat.eq_zero_or_pos (k 3 : ℕ) with h3 | h3
  · have hn : ¬ 0 < (k 3 : ℕ) := by omega
    rw [if_neg hn]
    simp only [nf, h3, if_true, mul_zero, add_zero]
    split_ifs <;> norm_num
  · have h3' : (k 3 : ℕ) ≠ 0 := h3.ne'
    have g3 := one_le_two_val h3
    simp only [if_pos h3, Hf, Lf_pred h3, Uf_pred h3]
    rcases Nat.eq_zero_or_pos (k 0 : ℕ) with h0 | h0 <;>
    rcases Nat.eq_zero_or_pos (k 1 : ℕ) with h1 | h1 <;>
    rcases Nat.eq_zero_or_pos (k 2 : ℕ) with h2 | h2
    · -- three summands at zero
      have hg : Gap k := by
        unfold Gap; rw [val_zero h0, val_zero h1, val_zero h2]; linarith
      simp [zf, nf, h0, h1, h2, h3', hg]
    · have hg : Gap k := by
        unfold Gap; rw [val_zero h0, val_zero h1]; linarith [val_add_le (k 2)]
      simp [zf, nf, h0, h1, h2.ne', h3', hg]
    · have hg : Gap k := by
        unfold Gap; rw [val_zero h0, val_zero h2]; linarith [val_add_le (k 1)]
      simp [zf, nf, h0, h1.ne', h2, h3', hg]
    · -- one summand at zero: the summands `k 1`, `k 2`
      by_cases c1 : (k 1 : ℕ) < (k 3 : ℕ)
      · have hg : Gap k := by
          unfold Gap; rw [val_zero h0]
          linarith [val_add_le (k 2), one_add_val_le c1]
        simp [zf, nf, h0, h1, h1.ne', h2.ne', h3', hg, c1, not_le.2 c1]
      · by_cases c2 : (k 2 : ℕ) < (k 3 : ℕ)
        · have hg : Gap k := by
            unfold Gap; rw [val_zero h0]
            linarith [val_add_le (k 1), one_add_val_le c2]
          simp [zf, nf, h0, h1, h1.ne', h2, h2.ne', h3', hg, c1, c2, not_lt.1 c1]
        · simp [zf, nf, h0, h1.ne', h2.ne', h3', c1, c2]
          split_ifs <;> norm_num
    · have hg : Gap k := by
        unfold Gap; rw [val_zero h1, val_zero h2]; linarith [val_add_le (k 0)]
      simp [zf, nf, h0.ne', h1, h2, h3', hg]
    · by_cases c1 : (k 0 : ℕ) < (k 3 : ℕ)
      · have hg : Gap k := by
          unfold Gap; rw [val_zero h1]
          linarith [val_add_le (k 2), one_add_val_le c1]
        simp [zf, nf, h0, h0.ne', h1, h2.ne', h3', hg, c1, not_le.2 c1]
      · by_cases c2 : (k 2 : ℕ) < (k 3 : ℕ)
        · have hg : Gap k := by
            unfold Gap; rw [val_zero h1]
            linarith [val_add_le (k 0), one_add_val_le c2]
          simp [zf, nf, h0, h0.ne', h1, h2, h2.ne', h3', hg, c1, c2, not_lt.1 c1]
        · simp [zf, nf, h0.ne', h1, h2.ne', h3', c1, c2]
          split_ifs <;> norm_num
    · by_cases c1 : (k 0 : ℕ) < (k 3 : ℕ)
      · have hg : Gap k := by
          unfold Gap; rw [val_zero h2]
          linarith [val_add_le (k 1), one_add_val_le c1]
        simp [zf, nf, h0, h0.ne', h1.ne', h2, h3', hg, c1, not_le.2 c1]
      · by_cases c2 : (k 1 : ℕ) < (k 3 : ℕ)
        · have hg : Gap k := by
            unfold Gap; rw [val_zero h2]
            linarith [val_add_le (k 0), one_add_val_le c2]
          simp [zf, nf, h0, h0.ne', h1, h1.ne', h2, h3', hg, c1, c2, not_lt.1 c1]
        · simp [zf, nf, h0.ne', h1.ne', h2, h3', c1, c2]
          split_ifs <;> norm_num
    · -- no summand at zero
      simp [zf, nf, h0.ne', h1.ne', h2.ne', h3']
      split_ifs <;> norm_num

theorem Ff_nonneg (k : Fin 4 → Fin (N + 1)) : 0 ≤ Ff k := by
  have hz : ∀ j : Fin (N + 1), 0 ≤ zf j := fun j => by unfold zf; split_ifs <;> norm_num
  have hn : ∀ j : Fin (N + 1), 0 ≤ nf j := fun j => by unfold nf; split_ifs <;> norm_num
  have he : ∀ t (j : Fin (N + 1)), 0 ≤ ef t j := fun t j => by unfold ef; split_ifs <;> norm_num
  have hL : ∀ t (j : Fin (N + 1)), 0 ≤ Lf t j := fun t j => by unfold Lf; split_ifs <;> norm_num
  have hU : ∀ t (j : Fin (N + 1)), 0 ≤ Uf t j := fun t j => by unfold Uf; split_ifs <;> norm_num
  have m3 : ∀ {a b c : ℝ}, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ a * b * c := fun ha hb hc =>
    mul_nonneg (mul_nonneg ha hb) hc
  unfold Ff Hf
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_)
    (Finset.sum_nonneg fun t _ => mul_nonneg ?_ (he t _))
  · exact mul_nonneg (m3 (hz _) (hz _) (hz _)) (hn _)
  · exact mul_nonneg (m3 (hz _) (hz _) (hn _)) (hn _)
  · exact mul_nonneg (m3 (hz _) (hn _) (hz _)) (hn _)
  · exact mul_nonneg (m3 (hn _) (hz _) (hz _)) (hn _)
  · exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (m3 (hz _) (hL _ _) (hn _)) (m3 (hz _) (hU _ _) (hL _ _)))
      (m3 (hL _ _) (hz _) (hn _))) (m3 (hU _ _) (hz _) (hL _ _)))
      (m3 (hL _ _) (hn _) (hz _))) (m3 (hU _ _) (hL _ _) (hz _))

/-! ### The mean of `Ff` -/

theorem sum_id (n : ℕ) : ∑ t ∈ range n, (t : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

theorem sum_sq (n : ℕ) : ∑ t ∈ range n, (t : ℝ) ^ 2 = (n - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- The mean of `Ff` under four independent indices: the paper's
`p^3 (1 - p) + 3 p^2 (1 - p)^2 + 2 p (1 - p)^3 (1 - O(1/N))`. -/
theorem int_Ff (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : 0 < N) :
    ∫ k, Ff k ∂(Measure.pi fun _ : Fin 4 => gridM p N)
      = p ^ 3 * (1 - p) + 3 * p ^ 2 * (1 - p) ^ 2
        + 3 * p * (1 - p) ^ 3 * (((N : ℝ) - 1) * (4 * N + 1) / (6 * N ^ 2)) := by
  have := gridM_prob hp0 hp1 hN
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : ∀ g : (Fin 4 → Fin (N + 1)) → ℝ,
      Integrable g (Measure.pi fun _ : Fin 4 => gridM p N) := fun g => Integrable.of_finite
  have hadd : ∀ g h : (Fin 4 → Fin (N + 1)) → ℝ,
      ∫ k, g k + h k ∂(Measure.pi fun _ : Fin 4 => gridM p N)
        = ∫ k, g k ∂(Measure.pi fun _ : Fin 4 => gridM p N)
          + ∫ k, h k ∂(Measure.pi fun _ : Fin 4 => gridM p N) :=
    fun g h => integral_add (hi g) (hi h)
  have hsum : ∀ g : Fin N → (Fin 4 → Fin (N + 1)) → ℝ,
      ∫ k, ∑ t : Fin N, g t k ∂(Measure.pi fun _ : Fin 4 => gridM p N)
        = ∑ t : Fin N, ∫ k, g t k ∂(Measure.pi fun _ : Fin 4 => gridM p N) :=
    fun g => integral_finset_sum _ fun t _ => hi (g t)
  have iE : ∀ t : Fin N, ∫ j, ef (t : ℕ) j ∂(gridM p N) = (1 - p) / N :=
    fun t => int_ef hp0 hp1 t.isLt
  have iL : ∀ t : Fin N, ∫ j, Lf (t : ℕ) j ∂(gridM p N) = (1 - p) / N * (t : ℕ) :=
    fun t => int_Lf hp0 hp1 t.isLt.le
  have iU : ∀ t : Fin N, ∫ j, Uf (t : ℕ) j ∂(gridM p N) = (1 - p) / N * ((N : ℝ) - (t : ℕ)) :=
    fun t => int_Uf hp0 hp1 t.isLt.le
  simp only [Ff, Hf, Finset.sum_range, add_mul, hadd, hsum, int4, int_zf hp0 hp1,
    int_nf hp0 hp1 hN, iE, iL, iU]
  have hcalc : ∀ t : Fin N,
      p * ((1 - p) / N * (t : ℕ)) * (1 - p) * ((1 - p) / N)
        + p * ((1 - p) / N * ((N : ℝ) - (t : ℕ))) * ((1 - p) / N * (t : ℕ)) * ((1 - p) / N)
        + (1 - p) / N * (t : ℕ) * p * (1 - p) * ((1 - p) / N)
        + (1 - p) / N * ((N : ℝ) - (t : ℕ)) * p * ((1 - p) / N * (t : ℕ)) * ((1 - p) / N)
        + (1 - p) / N * (t : ℕ) * (1 - p) * p * ((1 - p) / N)
        + (1 - p) / N * ((N : ℝ) - (t : ℕ)) * ((1 - p) / N * (t : ℕ)) * p * ((1 - p) / N)
      = 3 * p * (1 - p) ^ 3 / N ^ 3 * (2 * N * ((t : ℕ) : ℝ) - ((t : ℕ) : ℝ) ^ 2) := by
    intro t; field_simp; ring
  simp only [hcalc]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_range (fun t : ℕ => (t : ℝ)), ← Finset.sum_range (fun t : ℕ => (t : ℝ) ^ 2),
    sum_id, sum_sq]
  field_simp
  ring

end BeatAvg.Lower
