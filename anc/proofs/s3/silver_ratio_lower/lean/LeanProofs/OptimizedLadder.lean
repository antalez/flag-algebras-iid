module
public import LeanProofs.LowerBound
set_option linter.style.header false
@[expose] public section
noncomputable section
namespace Endpoint
namespace OptimizedLadder

def P (t : ℝ) : ℝ :=
  72*t^14 - 132*t^13 - 526*t^12 + 207*t^11 + 5374*t^10 - 8269*t^9 -
  11547*t^8 + 53262*t^7 - 87309*t^6 + 88506*t^5 - 60318*t^4 +
  27243*t^3 - 7695*t^2 + 1215*t - 81

def lo : ℝ := 81558932228969 / 100000000000000
def hi : ℝ := 81558932228970 / 100000000000000

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- Exact evaluations of a degree-14 polynomial at 14-digit rational endpoints.
theorem root_exists : ∃ t ∈ Set.Icc lo hi, P t = 0 := by
  have hc : Continuous P := by unfold P; fun_prop
  have hl : P lo ≤ 0 := by norm_num [P, lo]
  have hr : 0 ≤ P hi := by norm_num [P, hi]
  exact intermediate_value_Icc (by norm_num [lo, hi]) hc.continuousOn ⟨hl, hr⟩

/-- The algebraic candidate. The lower-bound proof needs existence, not
uniqueness of the root or global optimality of the mass parameters. -/
def theta : ℝ := Classical.choose root_exists

theorem theta_interval : theta ∈ Set.Icc lo hi := (Classical.choose_spec root_exists).1
theorem theta_root : P theta = 0 := (Classical.choose_spec root_exists).2

def z (t : ℝ) : ℝ := t * (2*t^2 - 6*t + 3) / (3*(t-1)*(3*t-1))
def p : ℝ := z theta / (1 + z theta)
def q : ℝ := theta / (1 + z theta)
def r : ℝ := (1 - theta) / (1 + z theta)
def value : ℝ := Ladder.F p q r / (1 - p^4)

theorem theta_coarse : (81 / 100 : ℝ) ≤ theta ∧ theta ≤ (82 / 100 : ℝ) := by
  have h := theta_interval
  simp only [Set.mem_Icc, lo, hi] at h
  constructor <;> linarith

theorem z_pos : 0 < z theta := by
  have ht := theta_coarse
  have ht0 : 0 < theta := by linarith
  have hnum : 2*theta^2 - 6*theta + 3 < 0 := by
    nlinarith [sq_nonneg (theta - 81/100), mul_nonneg (show 0 ≤ theta by linarith)
      (show 0 ≤ 82/100 - theta by linarith)]
  have hden : 3*(theta-1)*(3*theta-1) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg ht0 hnum) hden

theorem masses : 0 ≤ p ∧ 0 ≤ q ∧ 0 ≤ r ∧ p + q + r = 1 ∧ p < 1 := by
  have hz := z_pos
  have ht := theta_coarse
  have hd : 0 < 1 + z theta := by linarith
  have hdn := ne_of_gt hd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (div_pos hz hd).le
  · exact div_nonneg (by linarith : 0 ≤ theta) hd.le
  · exact div_nonneg (by linarith : 0 ≤ 1 - theta) hd.le
  · unfold p q r
    field_simp
    ring
  · exact (div_lt_one hd).mpr (by linarith)

/-- The exact algebraic ladder lower bound, not an assertion of sharpness. -/
theorem lower_bound : value ≤ finiteSup kappa := by
  rcases masses with ⟨hp, hq, hr, ht, hp1⟩
  exact ladder_lower p q r hp hq hr ht hp1

theorem probability_witness (e : ℝ) (he : 0 < e) :
    ∃ (α : Type) (f : Fintype α) (L : @Law α f),
      value - e < @Law.prob α f L kappa :=
  exists_near_lower kappa value e he lower_bound

set_option maxRecDepth 4096 in
/-- A separately certified decimal lower bound, using rational masses extremely
close to the algebraic candidate. No floating-point computation is trusted. -/
theorem numerical_lower : (4952063382580596903 / 10000000000000000000 : ℝ) < finiteSup kappa := by
  have h := ladder_lower (364616428198/1000000000000) (518212056720/1000000000000)
    (117171515082/1000000000000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  apply lt_of_lt_of_le _ h
  norm_num [Ladder.F]

end OptimizedLadder
end Endpoint
