module
public import LeanProofs.Amplification
public import LeanProofs.Ladder
set_option linter.style.header false
@[expose] public section
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace Endpoint

/-- All probabilities attained by finite nonnegative laws. The existential type
is just an atom-label type, not an extra restriction on locations or weights. -/
def attainable (c : ℝ) : Set ℝ :=
  {v | ∃ (α : Type) (f : Fintype α) (L : @Law α f), @Law.prob α f L c = v}

def finiteSup (c : ℝ) : ℝ := sSup (attainable c)

def zeroLaw : Law Unit where
  x _ := 0
  w _ := 1
  x_nonneg _ := le_rfl
  w_nonneg _ := by norm_num
  total := by simp

theorem attainable_nonempty (c : ℝ) : (attainable c).Nonempty :=
  ⟨zeroLaw.prob c, Unit, inferInstance, zeroLaw, rfl⟩

theorem attainable_bddAbove (c : ℝ) : BddAbove (attainable c) := by
  refine ⟨1, ?_⟩
  rintro v ⟨α, f, L, rfl⟩
  exact L.prob_le_one c

theorem prob_le_finiteSup {α : Type} [Fintype α] (L : Law α) (c : ℝ) :
    L.prob c ≤ finiteSup c :=
  le_csSup (attainable_bddAbove c) ⟨α, inferInstance, L, rfl⟩

theorem finiteSup_le_one (c : ℝ) : finiteSup c ≤ 1 :=
  csSup_le (attainable_nonempty c) (fun _ ⟨_, _, L, h⟩ => h ▸ L.prob_le_one c)

/-- Explicitly repeat the SAME base block a finite number of times. The
induction constructs the next law by replacing the base zero atom with the
previous law at a sufficiently small scale. -/
theorem finite_repetitions {α : Type} [Fintype α] (L : Law α) (c : ℝ)
    (z : α) (hz : L.x z = 0) (n : ℕ) :
    ∃ (β : Type) (f : Fintype β) (M : @Law β f),
      L.prob c * (∑ k ∈ Finset.range n, ((L.w z)^4)^k) ≤ @Law.prob β f M c := by
  induction n with
  | zero =>
    refine ⟨Unit, inferInstance, zeroLaw, ?_⟩
    simpa using zeroLaw.prob_nonneg c
  | succ n ih =>
    obtain ⟨β, f, M, hM⟩ := ih
    let := f
    obtain ⟨Q, hQ⟩ := L.exists_amplification M c z hz
    refine ⟨α × β, inferInstance, Q, ?_⟩
    have hm := mul_le_mul_of_nonneg_left hM (show 0 ≤ (L.w z)^4 by positivity)
    have hs : (∑ k ∈ Finset.range (n+1), ((L.w z)^4)^k) =
        1 + (L.w z)^4 * (∑ k ∈ Finset.range n, ((L.w z)^4)^k) := by
      rw [Finset.sum_range_succ']
      simp only [pow_succ, pow_zero, ← Finset.sum_mul]
      ring
    rw [hs]
    nlinarith

/-- The geometric repetition bound, proved using only finite laws. Arbitrarily
many repetitions suffice; no interchange of infinite sums and strict events
is assumed. -/
theorem amplified_lower {α : Type} [Fintype α] (L : Law α) (c : ℝ)
    (z : α) (hz : L.x z = 0) (hp : L.w z < 1) :
    L.prob c / (1 - (L.w z) ^ 4) ≤ finiteSup c := by
  have hp0 := L.w_nonneg z
  have hp4 : (L.w z) ^ 4 < 1 := pow_lt_one₀ hp0 hp (by norm_num)
  apply (div_le_iff₀ (by linarith : 0 < 1 - (L.w z) ^ 4)).mpr
  by_cases hzero : L.w z = 0
  · simpa [hzero] using prob_le_finiteSup L c
  have hpos : 0 < (L.w z) ^ 4 := pow_pos (lt_of_le_of_ne hp0 (Ne.symm hzero)) _
  have hs : finiteSup c ≤ (finiteSup c - L.prob c) / (L.w z) ^ 4 := by
    apply csSup_le (attainable_nonempty c)
    rintro v ⟨β, f, M, rfl⟩
    let := f
    obtain ⟨Q, hQ⟩ := L.exists_amplification M c z hz
    have hu := prob_le_finiteSup Q c
    apply (le_div_iff₀ hpos).mpr
    nlinarith
  have := (le_div_iff₀ hpos).mp hs
  nlinarith

/-- Every normalized nonnegative choice of p,q,r gives a ladder lower bound. -/
theorem ladder_lower (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (ht : p + q + r = 1) (hp1 : p < 1) :
    Ladder.F p q r / (1 - p ^ 4) ≤ finiteSup kappa := by
  have hd : 0 < 1 - p ^ 4 := by
    have := pow_lt_one₀ hp hp1 (show 4 ≠ 0 by decide)
    linarith
  have hn (n : ℕ) (hn : 0 < n) : Ladder.FN p q r n / (1 - p ^ 4) ≤ finiteSup kappa := by
    let L := Ladder.law n hn p q r hp hq hr ht
    have hL := amplified_lower L kappa none rfl hp1
    exact le_trans (div_le_div_of_nonneg_right (Ladder.law_lower n hn p q r hp hq hr ht)
      hd.le) hL
  have hlim : Tendsto (fun n : ℕ => Ladder.FN p q r n / (1 - p ^ 4)) atTop
      (𝓝 (Ladder.F p q r / (1 - p ^ 4))) := by
    have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hh := ((tendsto_const_nhds (x := Ladder.F p q r)).sub
      ((tendsto_const_nhds (x := (3 / 2 : ℝ) * q ^ 2 * r ^ 2)).mul hi)).div_const (1 - p ^ 4)
    simpa [Ladder.FN, div_eq_mul_inv] using hh
  exact le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, fun n hn' => hn n (by omega)⟩)

/-- An explicit finite probability witness arbitrarily close to any established
lower bound on the finite-law supremum. -/
theorem exists_near_lower (c B e : ℝ) (he : 0 < e) (hB : B ≤ finiteSup c) :
    ∃ (α : Type) (f : Fintype α) (L : @Law α f), B - e < @Law.prob α f L c := by
  have hh : B - e < sSup (attainable c) := by change B - e < finiteSup c; linarith
  obtain ⟨v, hv, hlt⟩ := exists_lt_of_lt_csSup (attainable_nonempty c) hh
  rcases hv with ⟨α, f, L, rfl⟩
  exact ⟨α, f, L, hlt⟩

theorem exists_ladder_lower (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (ht : p + q + r = 1) (hp1 : p < 1) (e : ℝ) (he : 0 < e) :
    ∃ (α : Type) (f : Fintype α) (L : @Law α f),
      Ladder.F p q r / (1 - p ^ 4) - e < @Law.prob α f L kappa :=
  exists_near_lower kappa _ e he (ladder_lower p q r hp hq hr ht hp1)

end Endpoint
