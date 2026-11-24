module
public import LeanProofs.FiniteLaw
set_option linter.style.header false
@[expose] public section
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace Endpoint
namespace Law

variable {α β : Type} [Fintype α] [Fintype β]

def zeroNoise (L : Law α) (M : Law β) (a : α) (b : β) : ℝ :=
  if L.x a = 0 then M.x b else 0

theorem zeroNoise_nonneg (L : Law α) (M : Law β) (a : α) (b : β) :
    0 ≤ zeroNoise L M a b := by
  unfold zeroNoise
  split_ifs
  · exact M.x_nonneg b
  · rfl

/-- Replace every zero location by a scaled draw from `M`, leaving positive
locations unchanged. Duplicate labels at unchanged locations are harmless. -/
def addScaled (L : Law α) (M : Law β) (e : ℝ) (he : 0 ≤ e) : Law (α × β) where
  x a := L.x a.1 + e * zeroNoise L M a.1 a.2
  w a := L.w a.1 * M.w a.2
  x_nonneg a := add_nonneg (L.x_nonneg _) (mul_nonneg he (zeroNoise_nonneg L M _ _))
  w_nonneg a := mul_nonneg (L.w_nonneg _) (M.w_nonneg _)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, L.total, M.total]

def zipQuad (a : Quad α) (b : Quad β) : Quad (α × β) :=
  ((a.1,b.1), (a.2.1,b.2.1), (a.2.2.1,b.2.2.1), (a.2.2.2,b.2.2.2))

def unzipEquiv : Quad (α × β) ≃ Quad α × Quad β where
  toFun a := ((a.1.1,a.2.1.1,a.2.2.1.1,a.2.2.2.1),
    (a.1.2,a.2.1.2,a.2.2.1.2,a.2.2.2.2))
  invFun a := zipQuad a.1 a.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem addScaled_weight (L : Law α) (M : Law β) (e : ℝ) (he : 0 ≤ e)
    (a : Quad α) (b : Quad β) :
    (L.addScaled M e he).weight (zipQuad a b) = L.weight a * M.weight b := by
  simp only [weight, addScaled, zipQuad]
  ring

theorem exists_preserves (L : Law α) (M : Law β) (c : ℝ) :
    ∃ e : ℝ, ∃ he : 0 < e, ∀ a b,
      L.wins c a → (L.addScaled M e he.le).wins c (zipQuad a b) := by
  have hh : ∀ᶠ e : ℝ in 𝓝 0, ∀ (a : Quad α) (b : Quad β), L.wins c a →
      (L.x a.1 + e * zeroNoise L M a.1 b.1) + (L.x a.2.1 + e * zeroNoise L M a.2.1 b.2.1) +
        (L.x a.2.2.1 + e * zeroNoise L M a.2.2.1 b.2.2.1) <
      c * (L.x a.2.2.2 + e * zeroNoise L M a.2.2.2 b.2.2.2) := by
    apply Filter.eventually_all.mpr
    intro a
    apply Filter.eventually_all.mpr
    intro b
    by_cases ha : L.wins c a
    · have hc₁ : ContinuousAt (fun e : ℝ =>
          (L.x a.1 + e * zeroNoise L M a.1 b.1) + (L.x a.2.1 + e * zeroNoise L M a.2.1 b.2.1) +
          (L.x a.2.2.1 + e * zeroNoise L M a.2.2.1 b.2.2.1)) 0 := by fun_prop
      have hc₂ : ContinuousAt (fun e : ℝ =>
          c * (L.x a.2.2.2 + e * zeroNoise L M a.2.2.2 b.2.2.2)) 0 := by fun_prop
      exact (hc₁.eventually_lt hc₂ (by simpa [wins] using ha)).mono (fun e h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => (ha h).elim)
  obtain ⟨d, hd, hb⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨d / 2, by linarith, ?_⟩
  have hm : d / 2 ∈ Metric.ball (0 : ℝ) d := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
    rw [abs_of_pos (by linarith : 0 < d / 2)]
    linarith
  exact hb hm

/-- Insert a sufficiently small independent copy at zero. All old strict successes survive;
when the four coarse labels equal the zero label, the fine law succeeds too. -/
theorem exists_amplification_scale (L : Law α) (M : Law β) (c : ℝ)
    (z : α) (hz : L.x z = 0) :
    ∃ e : ℝ, ∃ he : 0 < e,
      L.prob c + (L.w z) ^ 4 * M.prob c ≤ (L.addScaled M e he.le).prob c := by
  obtain ⟨e, he, hkeep⟩ := exists_preserves L M c
  let Q := L.addScaled M e he.le
  let zz : Quad α := (z,z,z,z)
  have hn : ¬ L.wins c zz := by simp [wins, zz, hz]
  have hzwin (b : Quad β) (h : M.wins c b) : Q.wins c (zipQuad zz b) := by
    change (L.x z + e * zeroNoise L M z b.1) + (L.x z + e * zeroNoise L M z b.2.1) +
      (L.x z + e * zeroNoise L M z b.2.2.1) < c * (L.x z + e * zeroNoise L M z b.2.2.2)
    simp only [zeroNoise, hz, ↓reduceIte, zero_add]
    have := mul_lt_mul_of_pos_left h he
    nlinarith only [this]
  have hprob : Q.prob c = ∑ a : Quad α, ∑ b : Quad β,
      if Q.wins c (zipQuad a b) then L.weight a * M.weight b else 0 := by
    unfold prob
    rw [← (unzipEquiv (α := α) (β := β)).symm.sum_comp]
    change (∑ ab : Quad α × Quad β,
      if Q.wins c (zipQuad ab.1 ab.2) then Q.weight (zipQuad ab.1 ab.2) else 0) = _
    rw [Fintype.sum_prod_type]
    simp only [Q, addScaled_weight]
  refine ⟨e, he, ?_⟩
  have hpoint (a : Quad α) (b : Quad β) :
      (if L.wins c a then L.weight a * M.weight b else 0) +
      (if a = zz then (if M.wins c b then L.weight a * M.weight b else 0) else 0) ≤
      (if Q.wins c (zipQuad a b) then L.weight a * M.weight b else 0) := by
    have hw := mul_nonneg (L.weight_nonneg a) (M.weight_nonneg b)
    by_cases ha : L.wins c a
    · have hne : a ≠ zz := by intro h; subst a; exact hn ha
      simp [ha, hne, hkeep a b ha, Q]
    · by_cases haz : a = zz
      · subst a
        by_cases hb : M.wins c b
        · simp [ha, hb, hzwin b hb]
        · simp only [ha, hb, ↓reduceIte, add_zero]
          split_ifs <;> linarith
      · simp only [ha, haz, ↓reduceIte, add_zero]
        split_ifs <;> linarith
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpoint a b))
  rw [← hprob] at hs
  have hid : (∑ a : Quad α, ∑ b : Quad β,
      ((if L.wins c a then L.weight a * M.weight b else 0) +
      (if a = zz then (if M.wins c b then L.weight a * M.weight b else 0) else 0))) =
      L.prob c + (L.w z) ^ 4 * M.prob c := by
    have hc (a : Quad α) : (∑ b : Quad β,
        if L.wins c a then L.weight a * M.weight b else 0) =
        if L.wins c a then L.weight a else 0 := by
      by_cases h : L.wins c a <;> simp [h, ← Finset.mul_sum, M.weight_total]
    have hf (a : Quad α) : (∑ b : Quad β,
        if a = zz then (if M.wins c b then L.weight a * M.weight b else 0) else 0) =
        if a = zz then L.weight a * M.prob c else 0 := by
      by_cases h : a = zz
      · simp only [h, ↓reduceIte, ← mul_ite_zero, ← Finset.mul_sum, prob]
      · simp only [h, ↓reduceIte, Finset.sum_const_zero]
    simp only [Finset.sum_add_distrib, hc, hf]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    change L.prob c + L.weight zz * M.prob c = _
    simp only [weight, zz]
    ring
  rwa [hid] at hs

theorem exists_amplification (L : Law α) (M : Law β) (c : ℝ)
    (z : α) (hz : L.x z = 0) :
    ∃ Q : Law (α × β), L.prob c + (L.w z) ^ 4 * M.prob c ≤ Q.prob c := by
  obtain ⟨e, he, h⟩ := L.exists_amplification_scale M c z hz
  exact ⟨L.addScaled M e he.le, h⟩

end Law
end Endpoint
