import Fast.Check8
import BeatAvg.Cert.CheckSound
import BeatAvg.Cert.IndexFacts
import BeatAvg.K8.Flags
import BeatAvg.K8.Acc

/-!
# Soundness of the kernel-friendly evaluation

For a sorted sample `ω` in general position with packed pattern `N`,
`evalZ U + 4 x · evalZ V = 4 · Dn · LamR(x)` where `(U, V) = lamUV t N`, for tables `t` that agree
with the certificate (`TbOk`).
-/

open Function

namespace BeatAvg.K8

open BeatAvg
open Fast (Z4)

/-- An arrangement as a list of natural numbers. -/
def nl (l : List (Fin 8)) : List ℕ := l.map Fin.val

theorem nl_getD (l : List (Fin 8)) (i : Fin 8) : (nl l).getD i.val 0 = (Fast.fnOf l i).val := by
  simp only [nl, Fast.fnOf]
  rw [show (0 : ℕ) = ((0 : Fin 8) : ℕ) from rfl, List.getD_map]

/-- The tables agree with the certificate. -/
structure TbOk (t : Tb) : Prop where
  sub5 : t.sub5 = sub5Spec
  sq : t.sq = Fast.repsSq.map fun l => compSq (nl l)
  deg : t.deg = Fast.repsDeg.map fun l => compDeg (nl l)
  thr : t.thr = Fast.repsThr.map fun l => compThr (nl l)
  obj : t.obj = Fast.repsObj.map fun l => compObj (nl l)
  flag : flagTabOk Fast.tabs8.ft t.ftP = true
  cls : clsTabOk Fast.tabs8.ct t.ctP = true
  clsB : ∀ k, k < 1215 → Nat.mod (Nat.shiftRight t.ctP (8 * k)) 256 < 150
  wq : 10 ≤ t.wQ
  wd : 10 ≤ t.wD
  wt : 13 ≤ t.wT
  qz : ∀ i j, i < 300 → j < 300 → Ent t.wQ (t.wQ - 10) 4 (entQ t i j) ∧
    entZ t.wQ t.offQ (entQ t i j) 0 = Fast.tabs8.QZ[i * 300 + j]!
  dt : ∀ c s, c < 150 → s < 5 → Ent t.wD (t.wD - 10) 8 (entD t c s) ∧
    entZ t.wD t.offD (entD t c s) 0
      = ((Fast.tabs8.loZ[c]!).mul ((Fast.Z4.ofInt (s : ℤ)).sub Fast.b4)).sub
          (Z4.smul (s : ℤ) (Fast.tabs8.hiZ[c]!)) ∧
    entZ t.wD t.offD (entD t c s) 4 = Fast.tabs8.hiZ[c]!
  tt : t.TT.length = 8 ∧ ∀ θ, θ < 8 →
    Ent t.wT (t.wT - 13) 8 (t.TT.getD θ (0, 0, 0)).1 ∧
    Ent t.wT (t.wT - 13) 8 (t.TT.getD θ (0, 0, 0)).2.1 ∧
    Ent t.wT (t.wT - 13) 8 (t.TT.getD θ (0, 0, 0)).2.2 ∧
    entZ t.wT t.offT (t.TT.getD θ (0, 0, 0)).1 0 = Z4.smul (-4) (Fast.tabs8.w1Z[θ]!) ∧
    entZ t.wT t.offT (t.TT.getD θ (0, 0, 0)).1 4 = Z4.zero ∧
    entZ t.wT t.offT (t.TT.getD θ (0, 0, 0)).2.1 0 = Z4.smul 4 (Fast.tabs8.w2Z[θ]!) ∧
    entZ t.wT t.offT (t.TT.getD θ (0, 0, 0)).2.1 4 = Z4.zero ∧
    entZ t.wT t.offT (t.TT.getD θ (0, 0, 0)).2.2 0
      = Z4.zero.sub ((Fast.tabs8.w2Z[θ]!).mul Fast.b4) ∧
    entZ t.wT t.offT (t.TT.getD θ (0, 0, 0)).2.2 4 = Fast.tabs8.w1Z[θ]!
  z8 : Ent t.wT (t.wT - 13) 8 (zero8 t.wT t.offT) ∧
    entZ t.wT t.offT (zero8 t.wT t.offT) 0 = Z4.zero ∧
    entZ t.wT t.offT (zero8 t.wT t.offT) 4 = Z4.zero
  dn : t.Dn = Fast.tabs8.Dn

/-- The compiled entry of a square term decomposes the two five-point configurations. -/
def sqChk (l : List (Fin 8)) : Bool :=
  let c := compSq (nl l)
  c.1 == 8 * (c.1 / 8) && c.2.1 == 9 * (c.2.1 / 9) && c.2.2.1 == 8 * (c.2.2.1 / 8) &&
    c.2.2.2 == 9 * (c.2.2.2 / 9) && decide (c.1 / 8 < 56) && decide (c.2.1 / 9 < 10) &&
    decide (c.2.2.1 / 8 < 56) && decide (c.2.2.2 / 9 < 10) &&
    ((List.finRange 5).all fun i => Fast.fnOf l (Fast.first5 i)
      == eOf (subs5.getD (c.1 / 8) []) (sigOf sigSqL (c.2.1 / 9) i)) &&
    ((List.finRange 5).all fun i => Fast.fnOf l (Fast.sel2 i)
      == eOf (subs5.getD (c.2.2.1 / 8) []) (sigOf sigSqL (c.2.2.2 / 9) i))

theorem subs5_getD_incr {S : ℕ} (hS : S < 56) : incr5 (subs5.getD S []) = true := by
  have hmem : subs5.getD S [] ∈ subs5 := by
    rw [List.getD_eq_getElem _ _ (by rw [subs5_length]; exact hS)]
    exact List.getElem_mem _
  exact List.all_eq_true.1 subs5_incr _ hmem

section Sample

variable {t : Tb} (ht : TbOk t) {ω : Fin 8 → ℝ} (hω : SG8 ω) (hD : (Fast.tabs8.Dn : ℝ) ≠ 0)

include ht hω in
/-- A flag read in the packed tables. -/
theorem flagAt_eq {S pq : ℕ} (hS : S < 56) (hpq : pq < 10) :
    flagAt t.ftP (codes (code 8 (extN ω)) t.sub5) (8 * S) (9 * pq)
      = Fast.Fflag Fast.tabs8.ft ((cfgOf ω).comap (eOf (subs5.getD S []) ∘ sigOf sigSqL pq)) % 300 := by
  rw [flag_of_tab ht.flag hω (subs5_getD_incr hS) hpq, ← codes_at ω hS, ht.sub5]
  rfl

include ht hω hD in
/-- A square term: the entry of the packed table is the entry of `Dn · Q`. -/
theorem sq_term {l : List (Fin 8)} (hc : sqChk l = true) :
    Ent t.wQ (t.wQ - 10) 4 (sqEnt t (codes (code 8 (extN ω)) t.sub5) (compSq (nl l))) ∧
    evalZ (entZ t.wQ t.offQ (sqEnt t (codes (code 8 (extN ω)) t.sub5) (compSq (nl l))) 0)
      = (Fast.tabs8.Dn : ℝ) * sqR (tabOf Fast.tabs8) (cfgOf ω) (Fast.fnOf l) := by
  simp only [sqChk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, h1⟩, h2⟩, h3⟩, h4⟩, hA⟩, hB⟩ := hc
  have fA : Fast.fnOf l ∘ Fast.first5
      = eOf (subs5.getD ((compSq (nl l)).1 / 8) []) ∘ sigOf sigSqL ((compSq (nl l)).2.1 / 9) :=
    funext fun i => hA i (List.mem_finRange i)
  have fB : Fast.fnOf l ∘ Fast.sel2
      = eOf (subs5.getD ((compSq (nl l)).2.2.1 / 8) []) ∘ sigOf sigSqL ((compSq (nl l)).2.2.2 / 9) :=
    funext fun i => hB i (List.mem_finRange i)
  have gA := flagAt_eq ht hω h1 h2
  have gB := flagAt_eq ht hω h3 h4
  rw [← e1, ← e2, ← fA] at gA
  rw [← e3, ← e4, ← fB] at gB
  have hqz := ht.qz _ _ (Nat.mod_lt (Fast.Fflag Fast.tabs8.ft ((cfgOf ω).comap (Fast.fnOf l ∘ Fast.first5)))
    (by norm_num : 0 < 300)) (Nat.mod_lt (Fast.Fflag Fast.tabs8.ft ((cfgOf ω).comap (Fast.fnOf l ∘ Fast.sel2)))
    (by norm_num : 0 < 300))
  simp only [sqEnt, gA, gB]
  refine ⟨hqz.1, ?_⟩
  rw [hqz.2]
  simp only [sqR, tabOf]
  rw [mul_div_cancel₀ _ hD]

/-- The compiled entry of a degree term decomposes the five-point configuration, and its two
atoms read the recorded quadruple. -/
def degChk (l : List (Fin 8)) : Bool :=
  let c := compDeg (nl l)
  c.1 == 8 * (c.1 / 8) && c.2.1 == 8 * (c.2.1 / 8) && decide (c.1 / 8 < 56) &&
    decide (c.2.1 / 8 < 5) &&
    ((List.finRange 5).all fun i => Fast.fnOf l (Fast.first5 i)
      == eOf (subs5.getD (c.1 / 8) []) (sigOf sigDegL (c.2.1 / 8) i)) &&
    compDegOk (nl l)

/-- The value of `s4C` for the trit `τ`, read in the packed triple of values. -/
theorem sv_case : ∀ m1 ∈ [0, 4, 6], ∀ m2 ∈ [0, 4, 6], ∀ τ ∈ [0, 1, 2],
    Nat.mod (Nat.shiftRight ((3 * bitAt m1 0 + bitAt m2 0) + 16 * (3 * bitAt m1 1 + bitAt m2 1)
        + 256 * (3 * bitAt m1 2 + bitAt m2 2)) (Nat.mul 4 τ)) 16
      = (if m1.testBit τ then 3 else 0) + (if m2.testBit τ then 1 else 0) := by
  decide

include ht hω in
theorem clsAt_eq {S p : ℕ} (hS : S < 56) (hp : p < 5) :
    clsAt t.ctP (codes (code 8 (extN ω)) t.sub5) (8 * S) (8 * p)
      = Fast.Fcls Fast.tabs8.ct ((cfgOf ω).comap (eOf (subs5.getD S []) ∘ sigOf sigDegL p)) := by
  rw [cls_of_tab ht.cls hω (subs5_getD_incr hS) hp, ← codes_at ω hS, ht.sub5]
  rfl

include hω in
/-- The value of `s4C`, read from the trit of the recorded quadruple. -/
theorem s4_eq {l : List (Fin 8)} (hc : compDegOk (nl l) = true) :
    Nat.mod (Nat.shiftRight (compDeg (nl l)).2.2.2
        (Nat.mul 4 (trS (code 8 (extN ω)) (compDeg (nl l)).2.2.1))) 16
      = Fast.s4C (cfgOf ω) (Fast.fnOf l) := by
  have g0 := nl_getD l 0
  have g5 := nl_getD l 5
  have g6 := nl_getD l 6
  have g7 := nl_getD l 7
  have v0 : ((0 : Fin 8) : ℕ) = 0 := rfl
  have v5 : ((5 : Fin 8) : ℕ) = 5 := rfl
  have v6 : ((6 : Fin 8) : ℕ) = 6 := rfl
  have v7 : ((7 : Fin 8) : ℕ) = 7 := rfl
  rw [v0] at g0; rw [v5] at g5; rw [v6] at g6; rw [v7] at g7
  have s1 := sb_atom hω (Fast.fnOf l 0) (Fast.fnOf l 5) (Fast.fnOf l 6) (Fast.fnOf l 7)
  have s2 := sb_atom hω (Fast.fnOf l 5) (Fast.fnOf l 6) (Fast.fnOf l 7) (Fast.fnOf l 0)
  have a1 := sbAtom_spec (Fast.fnOf l 0).val (Fast.fnOf l 5).val (Fast.fnOf l 6).val
    (Fast.fnOf l 7).val (Fin.isLt _) (Fin.isLt _) (Fin.isLt _) (Fin.isLt _)
  have a2 := sbAtom_spec (Fast.fnOf l 5).val (Fast.fnOf l 6).val (Fast.fnOf l 7).val
    (Fast.fnOf l 0).val (Fin.isLt _) (Fin.isLt _) (Fin.isLt _) (Fin.isLt _)
  rw [← g0, ← g5, ← g6, ← g7] at s1 s2 a1 a2
  simp only [compDegOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨hc1, hc2⟩ := hc
  simp only [Fast.s4C, s1, s2]
  generalize hA1 : sbAtom ((nl l).getD 0 0) ((nl l).getD 5 0) ((nl l).getD 6 0) ((nl l).getD 7 0)
    = A1 at hc1 a1 ⊢
  generalize hA2 : sbAtom ((nl l).getD 5 0) ((nl l).getD 6 0) ((nl l).getD 7 0) ((nl l).getD 0 0)
    = A2 at hc2 a2 ⊢
  have hsv : (compDeg (nl l)).2.2.2 = (3 * bitAt A1.2 0 + bitAt A2.2 0)
      + 16 * (3 * bitAt A1.2 1 + bitAt A2.2 1) + 256 * (3 * bitAt A1.2 2 + bitAt A2.2 2) := by
    simp only [compDeg, hA1, hA2]
  rw [hsv]
  have key : ∀ p, 2 * p = (compDeg (nl l)).2.2.1 →
      trS (code 8 (extN ω)) (compDeg (nl l)).2.2.1 = (pat 8 (extN ω)).getD p 0 := by
    intro p hp
    rw [← hp, trS_two, code, tr_packL _ _ (pat_small 8 _)]
  have hm1 : A1.2 ∈ [0, 4, 6] := by rcases a1.2 with h | h | h <;> simp [h]
  have hm2 : A2.2 ∈ [0, 4, 6] := by rcases a2.2 with h | h | h <;> simp [h]
  by_cases z1 : A1.2 = 0
  · by_cases z2 : A2.2 = 0
    · simp [z1, z2, bitAt, nmod]
    · have e2 := key _ (hc2.resolve_left z2)
      rw [e2]
      have ht2 := pat_getD_le (extN ω) A2.1
      rw [z1] at hm1 ⊢
      have := sv_case 0 (by simp) A2.2 hm2 ((pat 8 (extN ω)).getD A2.1 0)
        (by generalize (pat 8 (extN ω)).getD A2.1 0 = τ at ht2; interval_cases τ <;> simp)
      simpa using this
  · have e1 := key _ (hc1.resolve_left z1)
    rw [e1]
    have ht1 := pat_getD_le (extN ω) A1.1
    have hτ : (pat 8 (extN ω)).getD A1.1 0 ∈ [0, 1, 2] := by
      generalize (pat 8 (extN ω)).getD A1.1 0 = τ at ht1; interval_cases τ <;> simp
    have h := sv_case A1.2 hm1 A2.2 hm2 _ hτ
    rw [h]
    by_cases z2 : A2.2 = 0
    · simp [z2]
    · have e2 := key _ (hc2.resolve_left z2)
      rw [← e2, e1]

include ht hω hD in
/-- A degree term. -/
theorem deg_term {l : List (Fin 8)} (hc : degChk l = true) (x : ℝ) :
    Ent t.wD (t.wD - 10) 8
        (degEnt t (code 8 (extN ω)) (codes (code 8 (extN ω)) t.sub5) (compDeg (nl l))) ∧
    evalZ (entZ t.wD t.offD
          (degEnt t (code 8 (extN ω)) (codes (code 8 (extN ω)) t.sub5) (compDeg (nl l))) 0)
      + 4 * x * evalZ (entZ t.wD t.offD
          (degEnt t (code 8 (extN ω)) (codes (code 8 (extN ω)) t.sub5) (compDeg (nl l))) 4)
      = 4 * (Fast.tabs8.Dn : ℝ) * degR (tabOf Fast.tabs8) (cfgOf ω) (Fast.fnOf l) x := by
  simp only [degChk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨e1, e2⟩, h1⟩, h2⟩, hA⟩, hok⟩ := hc
  have fA : Fast.fnOf l ∘ Fast.first5
      = eOf (subs5.getD ((compDeg (nl l)).1 / 8) []) ∘ sigOf sigDegL ((compDeg (nl l)).2.1 / 8) :=
    funext fun i => hA i (List.mem_finRange i)
  have gA := clsAt_eq ht hω h1 h2
  rw [← e1, ← e2, ← fA] at gA
  have hs := s4_eq hω hok
  have hcls : clsAt t.ctP (codes (code 8 (extN ω)) t.sub5) (compDeg (nl l)).1 (compDeg (nl l)).2.1
      < 150 := by
    have hcd := codes_at ω h1
    have hlt := codeL3_le ω (eOf (subs5.getD ((compDeg (nl l)).1 / 8) []))
    rw [← ht.sub5, ← e1] at hcd
    simp only [clsAt, nadd, nmul]
    rw [hcd]
    have e : 40 * codeL3 (v5 ω (eOf (subs5.getD ((compDeg (nl l)).1 / 8) []))) + (compDeg (nl l)).2.1
        = 8 * (5 * codeL3 (v5 ω (eOf (subs5.getD ((compDeg (nl l)).1 / 8) [])))
          + (compDeg (nl l)).2.1 / 8) := by omega
    rw [e]
    exact ht.clsB _ (by omega)
  have hs5 : Fast.s4C (cfgOf ω) (Fast.fnOf l) < 5 := by
    unfold Fast.s4C; split_ifs <;> omega
  simp only [degEnt, hs]
  have hdt := ht.dt _ _ hcls hs5
  refine ⟨hdt.1, ?_⟩
  rw [hdt.2.1, hdt.2.2, gA]
  simp only [evalZ_sub, evalZ_mul, evalZ_smul, evalZ_ofInt, evalZ_b4, degR, tabOf]
  push_cast
  field_simp
  ring

/-! ### Threshold terms -/

def thrFR (l : List ℕ) : ℕ := forbF (sbAtom (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0))

def thrFS (l : List ℕ) : ℕ := forbT (sbAtom (l.getD 4 0) (l.getD 5 0) (l.getD 6 0) (l.getD 7 0))

def thrAB (l : List ℕ) (θ : ℕ) : ℕ :=
  Nat.lor (Nat.lor (belowF l θ 4) (belowF l θ 5)) (Nat.lor (belowF l θ 6) (belowF l θ 7))

def thrF (l : List ℕ) (θ : ℕ) : ℕ × ℕ × ℕ :=
  (Nat.lor (thrFR l) (Nat.lor (thrFS l) (thrAB l θ)),
    Nat.lor (thrFR l) (Nat.lor (thrFS l) (belowF l θ 7)), Nat.lor (thrFR l) (thrAB l θ))

theorem compThr_eq (l : List ℕ) : compThr l = (thrFR l, (List.range 8).map (thrF l)) := rfl

theorem clr_lor (H a b : ℕ) : clr H (Nat.lor a b) = (clr H a && clr H b) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, clr_iff, clr_iff, clr_iff, nlor, nland, nland, nland,
    clear_lor]

theorem clr_zero (H : ℕ) : clr H 0 = true := by
  rw [clr_iff, nland, Nat.and_zero]

include hω in
theorem sb_clrT (a b c d : Fin 8) :
    (cfgOf ω).sb a b c d
      = clr (hot (code 8 (extN ω))) (forbT (sbAtom a.val b.val c.val d.val)) := by
  rw [Bool.eq_iff_iff, clr_iff]
  exact sb_clearT hω a b c d

include hω in
theorem sb_clrF (a b c d : Fin 8) :
    (!(cfgOf ω).sb a b c d)
      = clr (hot (code 8 (extN ω))) (forbF (sbAtom a.val b.val c.val d.val)) := by
  rw [Bool.eq_iff_iff, clr_iff, Bool.not_eq_true']
  exact sb_clearF hω a b c d

theorem tripI_val (θ : ℕ) : (Fast.rootPos (Fast.tripI θ)).val = tripI θ := by
  unfold Fast.tripI tripI; split_ifs <;> rfl

theorem tripJ_val (θ : ℕ) : (Fast.rootPos (Fast.tripJ θ)).val = tripJ θ := by
  unfold Fast.tripJ tripJ; split_ifs <;> rfl

theorem tripK_val (θ : ℕ) : (Fast.rootPos (Fast.tripK θ)).val = tripK θ := by
  unfold Fast.tripK tripK; split_ifs <;> rfl

include hω in
/-- "Below the threshold" as a test on the one-hot pattern. -/
theorem below_clr (l : List (Fin 8)) (θ : ℕ) (p : Fin 8) :
    Fast.below (cfgOf ω) (Fast.fnOf l) θ p
      = clr (hot (code 8 (extN ω))) (belowF (nl l) θ p.val) := by
  have gp := nl_getD l p
  have gI := nl_getD l (Fast.rootPos (Fast.tripI θ))
  have gJ := nl_getD l (Fast.rootPos (Fast.tripJ θ))
  have gK := nl_getD l (Fast.rootPos (Fast.tripK θ))
  rw [tripI_val] at gI; rw [tripJ_val] at gJ; rw [tripK_val] at gK
  unfold Fast.below belowF
  simp only [gp, gI, gJ, gK]
  by_cases h4 : θ < 4
  · rw [ite_eq_left h4, ite_eq_left h4]
    exact sb_clrT hω _ _ _ _
  · rw [ite_eq_right h4, ite_eq_right h4]
    have hlt : (cfgOf ω).lt (Fast.fnOf l p) (Fast.fnOf l (Fast.rootPos (Fast.tripK θ)))
        = decide ((Fast.fnOf l p).val < (Fast.fnOf l (Fast.rootPos (Fast.tripK θ))).val) := by
      simp only [cfgOf]
      apply decide_eq_decide.2
      rw [hω.mono.lt_iff_lt, Fin.lt_def]
    rw [hlt]
    by_cases hc : (Fast.fnOf l p).val < (Fast.fnOf l (Fast.rootPos (Fast.tripK θ))).val
    · rw [ite_eq_left hc, clr_zero]
      simp [hc]
    · rw [ite_eq_right hc, ← sb_clrF hω]
      simp [hc]

theorem thrL_sum (H z : ℕ) (g : ℕ → ℝ) : ∀ (fs es : List (ℕ × ℕ × ℕ)),
    ((thrL H z fs es).map g).sum = ((fs.zip es).map fun p => g (sel H p.1.1 p.2.1 z)
      + g (sel H p.1.2.1 p.2.2.1 z) + g (sel H p.1.2.2 p.2.2.2 z)).sum
  | [], _ => by simp [thrL]
  | _ :: _, [] => by simp [thrL]
  | f :: fs, e :: es => by
    simp only [thrL, List.map_cons, List.sum_cons, List.zip_cons_cons, thrL_sum H z g fs es]
    ring

theorem thrL_length (H z : ℕ) : ∀ (fs es : List (ℕ × ℕ × ℕ)), fs.length = es.length →
    (thrL H z fs es).length = 3 * fs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | f :: fs, e :: es, h => by
    simp only [thrL, List.length_cons, thrL_length H z fs es (by simpa using h)]
    ring

theorem thrL_forall (H z : ℕ) (P : ℕ → Prop) (hz : P z) : ∀ (fs es : List (ℕ × ℕ × ℕ)),
    (∀ e ∈ es, P e.1 ∧ P e.2.1 ∧ P e.2.2) → ∀ x ∈ thrL H z fs es, P x
  | [], _, _ => by intro x hx; simp [thrL] at hx
  | _ :: _, [], _ => by intro x hx; simp [thrL] at hx
  | f :: fs, e :: es, h => by
    intro x hx
    have he := h e List.mem_cons_self
    have hsel : ∀ (F E : ℕ), P E → P (sel H F E z) := by
      intro F E hE
      rw [sel_eq]; cases clr H F <;> simpa
    simp only [thrL, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact hsel _ _ he.1
    · exact hsel _ _ he.2.1
    · exact hsel _ _ he.2.2
    · exact thrL_forall H z P hz fs es (fun e' he' => h e' (List.mem_cons_of_mem _ he')) x hx

theorem list_eq_range_map {α : Type} (l : List α) (d : α) {n : ℕ} (h : l.length = n) :
    l = (List.range n).map fun i => l.getD i d := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h1]

include hω in
theorem ty0_clr (l : List (Fin 8)) :
    Fast.ty0 (cfgOf ω) (Fast.fnOf l) = clr (hot (code 8 (extN ω))) (thrFR (nl l)) := by
  have h := sb_clrF hω (Fast.fnOf l 0) (Fast.fnOf l 1) (Fast.fnOf l 2) (Fast.fnOf l 3)
  rw [← nl_getD l 0, ← nl_getD l 1, ← nl_getD l 2, ← nl_getD l 3] at h
  exact h

include hω in
theorem succF_clr (l : List (Fin 8)) :
    Fast.succF (cfgOf ω) (Fast.fnOf l) = clr (hot (code 8 (extN ω))) (thrFS (nl l)) := by
  have h := sb_clrT hω (Fast.fnOf l 4) (Fast.fnOf l 5) (Fast.fnOf l 6) (Fast.fnOf l 7)
  rw [← nl_getD l 4, ← nl_getD l 5, ← nl_getD l 6, ← nl_getD l 7] at h
  exact h

include hω in
theorem allBelow_clr (l : List (Fin 8)) (θ : ℕ) :
    Fast.allBelow (cfgOf ω) (Fast.fnOf l) θ = clr (hot (code 8 (extN ω))) (thrAB (nl l) θ) := by
  unfold Fast.allBelow thrAB
  rw [clr_lor, clr_lor, clr_lor, below_clr hω l θ 4, below_clr hω l θ 5, below_clr hω l θ 6,
    below_clr hω l θ 7, Bool.and_assoc]
  rfl

set_option linter.unusedSimpArgs false in
include ht hω hD in
/-- A threshold term: the 24 entries added for an arrangement. -/
theorem thr_term (l : List (Fin 8)) (x : ℝ) :
    (thrEnts (hot (code 8 (extN ω))) (zero8 t.wT t.offT) t.TT (compThr (nl l))).length = 24 ∧
    (∀ e ∈ thrEnts (hot (code 8 (extN ω))) (zero8 t.wT t.offT) t.TT (compThr (nl l)),
      Ent t.wT (t.wT - 13) 8 e) ∧
    ((thrEnts (hot (code 8 (extN ω))) (zero8 t.wT t.offT) t.TT (compThr (nl l))).map
        fun e => evalZ (entZ t.wT t.offT e 0) + 4 * x * evalZ (entZ t.wT t.offT e 4)).sum
      = 4 * (Fast.tabs8.Dn : ℝ) * thrR (tabOf Fast.tabs8) (cfgOf ω) (Fast.fnOf l) x := by
  obtain ⟨hlen, htt⟩ := ht.tt
  obtain ⟨hz1, hz2, hz3⟩ := ht.z8
  have hTT := list_eq_range_map t.TT (0, 0, 0) hlen
  have hgz : evalZ (entZ t.wT t.offT (zero8 t.wT t.offT) 0)
      + 4 * x * evalZ (entZ t.wT t.offT (zero8 t.wT t.offT) 4) = 0 := by
    rw [hz2, hz3, evalZ_zero]; ring
  rw [compThr_eq]
  simp only [thrEnts]
  rw [← ty0_clr hω l]
  by_cases hty : Fast.ty0 (cfgOf ω) (Fast.fnOf l) = true
  · rw [hty, Bool.cond_true]
    refine ⟨?_, ?_, ?_⟩
    · rw [thrL_length _ _ _ _ (by rw [List.length_map, List.length_range, hlen])]
      simp
    · apply thrL_forall _ _ _ hz1
      intro e he
      rw [hTT] at he
      obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 he
      have := htt θ (List.mem_range.1 hθ)
      exact ⟨this.1, this.2.1, this.2.2.1⟩
    · rw [thrL_sum]
      nth_rewrite 1 [hTT]
      rw [List.zip_map', List.map_map, ← List.map_coe_finRange_eq_range, List.map_map,
        ← Fin.sum_univ_def, thrR, ite_eq_left hty, Finset.mul_sum]
      refine Finset.sum_congr rfl fun θ _ => ?_
      obtain ⟨-, -, -, h1, h2, h3, h4, h5, h6⟩ := htt θ.val θ.isLt
      have hb : Fast.below (cfgOf ω) (Fast.fnOf l) θ.val 7
          = clr (hot (code 8 (extN ω))) (belowF (nl l) θ.val 7) := below_clr hω l θ.val 7
      simp only [comp_apply, thrF, sel_eq, clr_lor, ← ty0_clr hω l, ← succF_clr hω l,
        ← allBelow_clr hω l, ← hb, hty, Bool.true_and]
      cases Fast.succF (cfgOf ω) (Fast.fnOf l) <;> cases Fast.allBelow (cfgOf ω) (Fast.fnOf l) θ.val <;>
        cases Fast.below (cfgOf ω) (Fast.fnOf l) θ.val 7 <;>
        simp only [Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.cond_true,
          Bool.cond_false, h1, h2, h3, h4, h5, h6, hgz, evalZ_smul, evalZ_zero, evalZ_sub,
          evalZ_mul, evalZ_b4, tabOf, ite_true, ite_false, Bool.false_eq_true] <;>
        (push_cast; field_simp; ring)
  · rw [Bool.not_eq_true] at hty
    rw [hty, Bool.cond_false]
    refine ⟨by simp, ?_, ?_⟩
    · intro e he
      rw [List.eq_of_mem_replicate he]
      exact hz1
    · rw [List.map_replicate, List.sum_replicate, hgz, thrR, hty]
      simp

/-! ### The four sums -/

theorem pow_headroom {w h n : ℕ} (hw : h ≤ w) (hn : n ≤ 2 ^ h) : n * 2 ^ (w - h) ≤ 2 ^ w := by
  calc n * 2 ^ (w - h) ≤ 2 ^ h * 2 ^ (w - h) := Nat.mul_le_mul_right _ hn
    _ = 2 ^ w := by rw [← pow_add]; congr 1; omega

theorem sum_flatMap_map {α : Type} (g : ℕ → ℝ) (f : α → List ℕ) : ∀ l : List α,
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_flatMap_map g f l]

theorem length_flatMap_const {α : Type} (f : α → List ℕ) (k : ℕ) : ∀ l : List α,
    (∀ a ∈ l, (f a).length = k) → (l.flatMap f).length = l.length * k
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      length_flatMap_const f k l (fun b hb => h b (List.mem_cons_of_mem _ hb)),
      h a List.mem_cons_self]
    ring

include ht hω hD in
theorem sq_total (L : List (List (Fin 8))) (hsq : t.sq = L.map fun l => compSq (nl l))
    (hL : L.length = 560) (hS : ∀ l ∈ L, sqChk l = true) :
    evalZ (decZ (sqAcc t (codes (code 8 (extN ω)) t.sub5) t.sq 0)
        t.wQ 0 (Nat.mul 560 t.offQ))
      = (Fast.tabs8.Dn : ℝ) * (L.map fun l => sqR (tabOf Fast.tabs8) (cfgOf ω) (Fast.fnOf l)).sum := by
  rw [sqAcc_eq, zero_add, hsq, List.map_map]
  simp only [Function.comp_def]
  obtain ⟨es, hes⟩ : ∃ es, es = L.map fun l =>
      sqEnt t (codes (code 8 (extN ω)) t.sub5) (compSq (nl l)) := ⟨_, rfl⟩
  rw [← hes]
  have hlen : es.length = 560 := by rw [hes, List.length_map]; exact hL
  have hE : ∀ e ∈ es, Ent t.wQ (t.wQ - 10) 4 e := by
    intro e he
    rw [hes] at he
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 he
    exact (sq_term ht hω hD (hS l hl)).1
  have hh : es.length * 2 ^ (t.wQ - 10) ≤ 2 ^ t.wQ := by
    rw [hlen]; exact pow_headroom ht.wq (by norm_num)
  rw [evalZ_decZ es t.offQ 0 560 hE hh (by norm_num) hlen.symm, hes, List.map_map,
    ← List.sum_map_mul_left]
  simp only [Function.comp_def]
  congr 1
  exact List.map_congr_left fun l hl => (sq_term ht hω hD (hS l hl)).2

include ht hω hD in
theorem deg_total (L : List (List (Fin 8))) (hdeg : t.deg = L.map fun l => compDeg (nl l))
    (hL : L.length = 840) (hS : ∀ l ∈ L, degChk l = true) (x : ℝ) :
    evalZ (decZ (degAcc t (code 8 (extN ω)) (codes (code 8 (extN ω)) t.sub5) t.deg 0) t.wD 0 (Nat.mul 840 t.offD))
      + 4 * x * evalZ (decZ (degAcc t (code 8 (extN ω)) (codes (code 8 (extN ω)) t.sub5) t.deg 0) t.wD 4 (Nat.mul 840 t.offD))
      = 4 * (Fast.tabs8.Dn : ℝ)
        * (L.map fun l => degR (tabOf Fast.tabs8) (cfgOf ω) (Fast.fnOf l) x).sum := by
  rw [degAcc_eq, zero_add, hdeg, List.map_map]
  simp only [Function.comp_def]
  obtain ⟨es, hes⟩ : ∃ es, es = L.map fun l => degEnt t (code 8 (extN ω))
      (codes (code 8 (extN ω)) t.sub5) (compDeg (nl l)) := ⟨_, rfl⟩
  rw [← hes]
  have hlen : es.length = 840 := by rw [hes, List.length_map]; exact hL
  have hE : ∀ e ∈ es, Ent t.wD (t.wD - 10) 8 e := by
    intro e he
    rw [hes] at he
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 he
    exact (deg_term ht hω hD (hS l hl) x).1
  have hh : es.length * 2 ^ (t.wD - 10) ≤ 2 ^ t.wD := by
    rw [hlen]; exact pow_headroom ht.wd (by norm_num)
  rw [evalZ_decZ es t.offD 0 840 hE hh (by norm_num) hlen.symm,
    evalZ_decZ es t.offD 4 840 hE hh (by norm_num) hlen.symm,
    ← List.sum_map_mul_left, ← List.sum_map_add, hes, List.map_map, ← List.sum_map_mul_left]
  simp only [Function.comp_def]
  congr 1
  exact List.map_congr_left fun l hl => (deg_term ht hω hD (hS l hl) x).2

include ht hω hD in
theorem thr_total (L : List (List (Fin 8))) (hthr : t.thr = L.map fun l => compThr (nl l))
    (hL : L.length = 280) (x : ℝ) :
    evalZ (decZ (thrAcc t (hot (code 8 (extN ω))) (zero8 t.wT t.offT)
          (Nat.mul 24 (zero8 t.wT t.offT)) t.thr 0) t.wT 0 (Nat.mul 6720 t.offT))
      + 4 * x * evalZ (decZ (thrAcc t (hot (code 8 (extN ω))) (zero8 t.wT t.offT)
          (Nat.mul 24 (zero8 t.wT t.offT)) t.thr 0) t.wT 4 (Nat.mul 6720 t.offT))
      = 4 * (Fast.tabs8.Dn : ℝ)
        * (L.map fun l => thrR (tabOf Fast.tabs8) (cfgOf ω) (Fast.fnOf l) x).sum := by
  rw [thrAcc_eq, zero_add, hthr, List.flatMap_map]
  obtain ⟨es, hes⟩ : ∃ es, es = L.flatMap fun l => thrEnts (hot (code 8 (extN ω)))
      (zero8 t.wT t.offT) t.TT (compThr (nl l)) := ⟨_, rfl⟩
  rw [← hes]
  have hlen : es.length = 6720 := by
    rw [hes, length_flatMap_const _ 24 _ fun l _ => (thr_term ht hω hD l x).1, hL]
  have hE : ∀ e ∈ es, Ent t.wT (t.wT - 13) 8 e := by
    intro e he
    rw [hes] at he
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.1 he
    exact (thr_term ht hω hD l x).2.1 e hl
  have hh : es.length * 2 ^ (t.wT - 13) ≤ 2 ^ t.wT := by
    rw [hlen]; exact pow_headroom ht.wt (by norm_num)
  rw [evalZ_decZ es t.offT 0 6720 hE hh (by norm_num) hlen.symm,
    evalZ_decZ es t.offT 4 6720 hE hh (by norm_num) hlen.symm,
    ← List.sum_map_mul_left, ← List.sum_map_add, hes, sum_flatMap_map, ← List.sum_map_mul_left]
  congr 1
  exact List.map_congr_left fun l _ => (thr_term ht hω hD l x).2.2

include hω in
theorem obj_total (L : List (List (Fin 8))) (hobj : t.obj = L.map fun l => compObj (nl l)) :
    objCnt (hot (code 8 (extN ω))) t.obj 0
      = L.countP fun l => Fast.succA (cfgOf ω) (Fast.fnOf l) := by
  rw [objCnt_eq, zero_add, hobj, List.countP_map]
  congr 1
  funext l
  have h := sb_clrT hω (Fast.fnOf l 0) (Fast.fnOf l 1) (Fast.fnOf l 2) (Fast.fnOf l 3)
  rw [← nl_getD l 0, ← nl_getD l 1, ← nl_getD l 2, ← nl_getD l 3] at h
  exact h.symm

/-- The checks on the arrangements that the proof uses. -/
structure RepsOk : Prop where
  sq : ∀ l ∈ Fast.repsSq, sqChk l = true
  deg : ∀ l ∈ Fast.repsDeg, degChk l = true

include ht hω hD in
/-- **The kernel-friendly evaluation computes the functional.** -/
theorem lamUV_sound (hR : RepsOk) (x : ℝ) :
    evalZ (lamUV t (code 8 (extN ω))).1 + 4 * x * evalZ (lamUV t (code 8 (extN ω))).2
      = 4 * (Fast.tabs8.Dn : ℝ) * LamR (tabOf Fast.tabs8) (cfgOf ω) x := by
  have h1 := sq_total ht hω hD Fast.repsSq ht.sq sq_facts.length hR.sq
  have h2 := deg_total ht hω hD Fast.repsDeg ht.deg deg_facts.length hR.deg x
  have h3 := thr_total ht hω hD Fast.repsThr ht.thr thr_facts.length x
  have h4 := obj_total hω Fast.repsObj ht.obj
  have hobj := sum_map_ite_countP Fast.repsObj fun l => Fast.succA (cfgOf ω) (Fast.fnOf l)
  simp only [lamUV, evalZ_add, evalZ_smul, evalZ_ofInt, h4, ht.dn]
  unfold LamR
  rw [hobj]
  push_cast
  linear_combination 288 * h1 + 48 * h2 + 144 * h3

end Sample

/-- **Soundness of the leaf check.** If the packed pattern of a sorted sample passes `leafOk`, the
two inequalities of the two-point criterion hold for the sample. -/
theorem leafOk_sound {t : Tb} (ht : TbOk t) (hR : RepsOk) (he : Encl t.encLo t.encHi t.encM)
    (hDn : 0 < Fast.tabs8.Dn) {p q e : ℤ} (hq : 0 < q) {ω : Fin 8 → ℝ} (hω : SG8 ω)
    (h : leafOk t p q e (code 8 (extN ω)) = true) :
    Lam (tabOf Fast.tabs8).D Bstar ω ≤ Bstar ∧
      Lam (tabOf Fast.tabs8).D ((p : ℝ) / q) ω ≤ ((p : ℝ) - e) / q := by
  have hD : (0 : ℝ) < (Fast.tabs8.Dn : ℝ) := by exact_mod_cast hDn
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  simp only [leafOk, Bool.and_eq_true] at h
  obtain ⟨hB, hC⟩ := h
  constructor
  · have h1 := nonneg_sound he hB
    simp only [evalZ_sub, evalZ_smul, evalZ_mul, evalZ_b4, ht.dn] at h1
    have h2 := lamUV_sound ht hω hD.ne' hR Bstar
    rw [Lam_sorted _ hω, fact8]
    push_cast at h1
    have h3 : (Fast.tabs8.Dn : ℝ) * LamR (tabOf Fast.tabs8) (cfgOf ω) Bstar
        ≤ (Fast.tabs8.Dn : ℝ) * (40320 * Bstar) := by nlinarith
    have h4 := le_of_mul_le_mul_left h3 hD
    rw [one_div, inv_mul_le_iff₀ (by norm_num)]
    linarith
  · have h1 := nonneg_sound he hC
    simp only [evalZ_sub, evalZ_smul, evalZ_ofInt, ht.dn] at h1
    have h2 := lamUV_sound ht hω hD.ne' hR ((p : ℝ) / q)
    rw [Lam_sorted _ hω, fact8]
    push_cast at h1
    have h2' : (q : ℝ) * evalZ (lamUV t (code 8 (extN ω))).1
        + 4 * p * evalZ (lamUV t (code 8 (extN ω))).2
        = q * (4 * Fast.tabs8.Dn * LamR (tabOf Fast.tabs8) (cfgOf ω) ((p : ℝ) / q)) := by
      rw [← h2]; field_simp
    have h3 : (4 * (Fast.tabs8.Dn : ℝ) * q) * LamR (tabOf Fast.tabs8) (cfgOf ω) ((p : ℝ) / q)
        ≤ (4 * (Fast.tabs8.Dn : ℝ) * q) * (40320 * (((p : ℝ) - e) / q)) := by
      have : (4 * (Fast.tabs8.Dn : ℝ) * q) * (40320 * (((p : ℝ) - e) / q))
          = 4 * Fast.tabs8.Dn * 40320 * ((p : ℝ) - e) := by field_simp
      rw [this]
      nlinarith
    have h4 := le_of_mul_le_mul_left h3 (by positivity)
    rw [one_div, inv_mul_le_iff₀ (by norm_num)]
    linarith

end BeatAvg.K8
