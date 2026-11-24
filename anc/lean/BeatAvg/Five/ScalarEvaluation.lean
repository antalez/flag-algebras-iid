import BeatAvg.Five.ColorFacts
import BeatAvg.Cert.DegTerm
import Fast.Five.Arrangements

open MeasureTheory Set Function
namespace BeatAvg.Five
open Fast.Five

theorem bitNat_cast (b : Bool) : (bitNat b : ℝ) = if b then 1 else 0 := by cases b <;> norm_num [bitNat]

def classCode (c : Config 5) (ρ : Fin 5 → Fin 5) : ℕ :=
  (if c.close (ρ 0) (ρ 1) then 2 else 0) + (if c.additive.lt (ρ 0) (ρ 1) then 0 else 1)
def degreeCount (c : Config 5) (ρ : Fin 5 → Fin 5) : ℕ :=
  3*bitNat (c.additive.sb (ρ 0) (ρ 2) (ρ 3) (ρ 4)) + bitNat (c.additive.sb (ρ 2) (ρ 3) (ρ 4) (ρ 0))
def halfCode (c : Config 5) (ρ : Fin 5 → Fin 5) : Bool :=
  [1,2,3,4].all fun i => c.additive.lt (ρ i) (ρ 0) && !(c.close (ρ i) (ρ 0))
def twiceCode (c : Config 5) (ρ : Fin 5 → Fin 5) : Bool :=
  [1,2,3,4].all fun i => c.additive.lt (ρ i) (ρ 0) || c.close (ρ i) (ρ 0)
def goodCode (c : Config 5) (ρ : Fin 5 → Fin 5) : Bool :=
  c.additive.sb (ρ 1) (ρ 2) (ρ 3) (ρ 4)

theorem s4_config (v : Fin 5 → ℝ) {ρ : Fin 5 → Fin 5} (hρ : Injective ρ) :
    s4 (splitDegree (v ∘ ρ)).1 (splitDegree (v ∘ ρ)).2.2 = (degreeCount (configOf v) ρ : ℝ) := by
  rw [s4_formula]
  have h1 := sb_cfgOf v (a := ρ 0) (b := ρ 2) (c := ρ 3) (d := ρ 4)
    (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide))
    (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide))
  have h2 := sb_cfgOf v (a := ρ 2) (b := ρ 3) (c := ρ 4) (d := ρ 0)
    (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide))
    (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide))
  change 3*(if v (ρ 0)+(v (ρ 2)+v (ρ 3)) < 2*v (ρ 4) then (1 : ℝ) else 0) +
    (if v (ρ 2)+v (ρ 3)+v (ρ 4) < 2*v (ρ 0) then 1 else 0) = _
  simp only [degreeCount, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, bitNat_cast, h1, h2]
  simp [configOf, h1, h2, add_assoc]

theorem degreeSample_eval (v : Fin 5 → ℝ) {ρ : Fin 5 → Fin 5} (hρ : Injective ρ) :
    degreeSample (v ∘ ρ) = (Data.nu[classCode (configOf v) ρ]?.getD 0 : ℚ) *
      ((degreeCount (configOf v) ρ : ℝ)/4-Bstar) := by
  unfold degreeSample degreeTerm pairWeight
  change (Data.nu[pairClass (v (ρ 0),v (ρ 1))]?.getD 0 : ℚ) *
    (s4 (splitDegree (v ∘ ρ)).1 (splitDegree (v ∘ ρ)).2.2 / 4-Bstar) = _
  rw [s4_config v hρ, class_eq (hρ.ne (by decide : (0 : Fin 5) ≠ 1))]
  rfl

theorem halfCode_spec {v : Fin 5 → ℝ} (hv : Generic v) {ρ : Fin 5 → Fin 5} (hρ : Injective ρ) :
    halfCode (configOf v) ρ = true ↔ splitTail (v ∘ ρ) ∈ tailAll (1/2) := by
  simp only [halfCode, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  have h1 := half_below_iff hv (hρ.ne (by decide : (1 : Fin 5) ≠ 0))
  have h2 := half_below_iff hv (hρ.ne (by decide : (2 : Fin 5) ≠ 0))
  have h3 := half_below_iff hv (hρ.ne (by decide : (3 : Fin 5) ≠ 0))
  have h4 := half_below_iff hv (hρ.ne (by decide : (4 : Fin 5) ≠ 0))
  simp only [Bool.and_eq_true] at h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  simp [tailAll, splitTail, split, e14, Fin.forall_fin_succ, div_eq_mul_inv, mul_comm]
  rfl

theorem twiceCode_spec {v : Fin 5 → ℝ} (hv : Generic v) {ρ : Fin 5 → Fin 5} (hρ : Injective ρ) :
    twiceCode (configOf v) ρ = true ↔ splitTail (v ∘ ρ) ∈ tailAll 2 := by
  simp only [twiceCode, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  rw [twice_below_iff hv (hρ.ne (by decide : (1 : Fin 5) ≠ 0)),
    twice_below_iff hv (hρ.ne (by decide : (2 : Fin 5) ≠ 0)),
    twice_below_iff hv (hρ.ne (by decide : (3 : Fin 5) ≠ 0)),
    twice_below_iff hv (hρ.ne (by decide : (4 : Fin 5) ≠ 0))]
  simp [tailAll, splitTail, split, e14, Fin.forall_fin_succ]
  rfl

theorem goodCode_spec (v : Fin 5 → ℝ) {ρ : Fin 5 → Fin 5} (hρ : Injective ρ) :
    goodCode (configOf v) ρ = true ↔ (splitTail (v ∘ ρ)).2 ∈ S4 :=
  sb_cfgOf v (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide))
    (hρ.ne (by decide)) (hρ.ne (by decide)) (hρ.ne (by decide))

theorem tailSample_eval (v : Fin 5 → ℝ) {ρ : Fin 5 → Fin 5} (hρ : Injective ρ)
    (q x : ℝ) (b : Bool) (hb : b = true ↔ splitTail (v ∘ ρ) ∈ tailAll q) :
    tailSample q x (v ∘ ρ) = if b then x-(bitNat (goodCode (configOf v) ρ) : ℝ) else 0 := by
  have hA := ind_eq_ite_bool hb.symm
  have hW : splitTail (v ∘ ρ) ∈ tailWin q ↔ (b && goodCode (configOf v) ρ) = true := by
    simp only [tailWin, Set.mem_ofPred_eq, Bool.and_eq_true, hb, goodCode_spec v hρ]
    exact and_comm
  have hW' := ind_eq_ite_bool hW
  unfold tailSample tailTerm
  rw [hA, hW', bitNat_cast]
  cases b <;> cases goodCode (configOf v) ρ <;> simp

theorem objective_eval (v : Fin 5 → ℝ) {ρ : Fin 5 → Fin 5} (hρ : Injective ρ) :
    objective (v ∘ ρ) = (bitNat ((configOf v).additive.sb (ρ 0) (ρ 1) (ρ 2) (ρ 3)) : ℝ) := by
  rw [bitNat_cast]
  exact objG_eval firstFour v (hρ.comp (by intro a b h; exact Fin.ext (congrArg (Fin.val : Fin 5 → ℕ) h)))

noncomputable def scalarSample (x : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  objective v + degreeSample v + (Data.wHalf : ℝ)*tailSample (1/2) x v +
    (Data.wTwice : ℝ)*tailSample 2 x v

theorem scalarSample_eval {v : Fin 5 → ℝ} (hv : Generic v) {ρ : Fin 5 → Fin 5}
    (hρ : Injective ρ) (x : Fast.K) :
    scalarSample (evalK x) (v ∘ ρ) =
      evalK (scalarCode Data.blocks Data.wHalf Data.wTwice Data.nu (configOf v) ρ x) := by
  rw [scalarSample, objective_eval v hρ, degreeSample_eval v hρ,
    tailSample_eval v hρ (1/2) (evalK x) _ (halfCode_spec hv hρ),
    tailSample_eval v hρ 2 (evalK x) _ (twiceCode_spec hv hρ)]
  change _ = evalK ((Fast.K.ofRat (bitNat ((configOf v).additive.sb (ρ 0) (ρ 1) (ρ 2) (ρ 3)))).add
    ((((Fast.K.ofRat ((degreeCount (configOf v) ρ : ℚ)/4)).sub Fast.K.bstar).smul
      (Data.nu[classCode (configOf v) ρ]?.getD 0)).add
      ((if halfCode (configOf v) ρ then
        (x.sub (Fast.K.ofRat (bitNat (goodCode (configOf v) ρ)))).smul Data.wHalf else Fast.K.zero).add
      (if twiceCode (configOf v) ρ then
        (x.sub (Fast.K.ofRat (bitNat (goodCode (configOf v) ρ)))).smul Data.wTwice else Fast.K.zero))))
  cases hh : halfCode (configOf v) ρ <;> cases ht : twiceCode (configOf v) ρ <;>
    simp only [hh, ht, Bool.false_eq_true, if_false, if_true,
      evalK_add, evalK_sub, evalK_smul, evalK_ofRat, evalK_bstar, evalK_zero,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] <;> ring

end BeatAvg.Five
