import BeatAvg.Cert.CertValid
import BeatAvg.K8.EvalSound

/-!
# Checks of the tables, as boolean functions that the kernel evaluates
-/

namespace BeatAvg.K8

open BeatAvg
open Fast (Z4)

def z4eq (x y : Z4) : Bool :=
  decide (x.a = y.a) && decide (x.b = y.b) && decide (x.c = y.c) && decide (x.d = y.d)

theorem z4eq_eq {x y : Z4} (h : z4eq x y = true) : x = y := by
  simp only [z4eq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases x; cases y
  simp_all

/-- `K` fields of `w` bits, each below `2 ^ w0`. -/
def entB (w w0 K e : ℕ) : Bool :=
  decide (e < (2 ^ w) ^ K) && (List.range K).all fun k => decide (fieldAt w e k < 2 ^ w0)

theorem entB_ent {w w0 K e : ℕ} (h : entB w w0 K e = true) : Ent w w0 K e := by
  simp only [entB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact h

/-- Row `i` of the packed table of `Dn · Q` against the certificate. -/
def qRowOk (t : Tb) (i : ℕ) : Bool :=
  (List.range 300).all fun j =>
    entB t.wQ (t.wQ - 10) 4 (entQ t i j) &&
      z4eq (entZ t.wQ t.offQ (entQ t i j) 0) ((Fast.QK Fast.cert8 i j).toZ4 Fast.cert8.Dn)

theorem QZ_at' (c : Fast.Cert8) {i j : ℕ} (hi : i < 300) (hj : j < 300) :
    (Fast.tabsOf c).QZ[i * 300 + j]! = (Fast.QK c i j).toZ4 c.Dn := by
  have hk : i * 300 + j < 90000 := by omega
  have hQZ : (Fast.tabsOf c).QZ = Array.ofFn (Fast.qzFn c) := by
    simp only [Fast.tabsOf]
  have e1 : (i * 300 + j) / 300 = i := by omega
  have e2 : (i * 300 + j) % 300 = j := by omega
  rw [hQZ, ofFn_getElem! (Fast.qzFn c) _ hk]
  simp only [Fast.qzFn, Fast.qzAt, e1, e2]

theorem QZ_at {i j : ℕ} (hi : i < 300) (hj : j < 300) :
    Fast.tabs8.QZ[i * 300 + j]! = (Fast.QK Fast.cert8 i j).toZ4 Fast.cert8.Dn :=
  QZ_at' Fast.cert8 hi hj

theorem qz_of_rows {t : Tb} (h : ∀ i, i < 300 → qRowOk t i = true) :
    ∀ i j, i < 300 → j < 300 → Ent t.wQ (t.wQ - 10) 4 (entQ t i j) ∧
      entZ t.wQ t.offQ (entQ t i j) 0 = Fast.tabs8.QZ[i * 300 + j]! := by
  intro i j hi hj
  have := h i hi
  simp only [qRowOk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at this
  obtain ⟨h1, h2⟩ := this j hj
  exact ⟨entB_ent h1, by rw [QZ_at hi hj]; exact z4eq_eq h2⟩

/-- The packed degree table against the certificate. -/
def dtOk (t : Tb) : Bool :=
  (List.range 150).all fun c => (List.range 5).all fun s =>
    entB t.wD (t.wD - 10) 8 (entD t c s) &&
      z4eq (entZ t.wD t.offD (entD t c s) 0)
        (((Fast.tabs8.loZ[c]!).mul ((Fast.Z4.ofInt (s : ℤ)).sub Fast.b4)).sub
          (Z4.smul (s : ℤ) (Fast.tabs8.hiZ[c]!))) &&
      z4eq (entZ t.wD t.offD (entD t c s) 4) (Fast.tabs8.hiZ[c]!)

/-- The packed threshold entries against the certificate. -/
def ttOk (t : Tb) : Bool :=
  t.TT.length == 8 && (List.range 8).all fun θ =>
    entB t.wT (t.wT - 13) 8 (t.TT.getD θ (0, 0, 0)).1 &&
    entB t.wT (t.wT - 13) 8 (t.TT.getD θ (0, 0, 0)).2.1 &&
    entB t.wT (t.wT - 13) 8 (t.TT.getD θ (0, 0, 0)).2.2 &&
    z4eq (entZ t.wT t.offT (t.TT.getD θ (0, 0, 0)).1 0) (Z4.smul (-4) (Fast.tabs8.w1Z[θ]!)) &&
    z4eq (entZ t.wT t.offT (t.TT.getD θ (0, 0, 0)).1 4) Z4.zero &&
    z4eq (entZ t.wT t.offT (t.TT.getD θ (0, 0, 0)).2.1 0) (Z4.smul 4 (Fast.tabs8.w2Z[θ]!)) &&
    z4eq (entZ t.wT t.offT (t.TT.getD θ (0, 0, 0)).2.1 4) Z4.zero &&
    z4eq (entZ t.wT t.offT (t.TT.getD θ (0, 0, 0)).2.2 0)
      (Z4.zero.sub ((Fast.tabs8.w2Z[θ]!).mul Fast.b4)) &&
    z4eq (entZ t.wT t.offT (t.TT.getD θ (0, 0, 0)).2.2 4) (Fast.tabs8.w1Z[θ]!)

/-- The small checks: zero entry, class bound, widths, common denominator. -/
def miscOk (t : Tb) : Bool :=
  entB t.wT (t.wT - 13) 8 (zero8 t.wT t.offT) &&
    z4eq (entZ t.wT t.offT (zero8 t.wT t.offT) 0) Z4.zero &&
    z4eq (entZ t.wT t.offT (zero8 t.wT t.offT) 4) Z4.zero &&
    ((List.range 1215).all fun k => decide (Nat.mod (Nat.shiftRight t.ctP (8 * k)) 256 < 150)) &&
    decide (10 ≤ t.wQ) && decide (10 ≤ t.wD) && decide (13 ≤ t.wT) &&
    decide (t.Dn = Fast.tabs8.Dn)

/-- The tables agree with the certificate, from the checks. -/
theorem tbOk_of {t : Tb} (h1 : t.sub5 = sub5Spec)
    (h2 : t.sq = Fast.repsSq.map fun l => compSq (nl l))
    (h3 : t.deg = Fast.repsDeg.map fun l => compDeg (nl l))
    (h4 : t.thr = Fast.repsThr.map fun l => compThr (nl l))
    (h5 : t.obj = Fast.repsObj.map fun l => compObj (nl l))
    (h6 : flagTabOk Fast.tabs8.ft t.ftP = true) (h7 : clsTabOk Fast.tabs8.ct t.ctP = true)
    (h8 : ∀ i, i < 300 → qRowOk t i = true) (h9 : dtOk t = true) (h10 : ttOk t = true)
    (h11 : miscOk t = true) : TbOk t := by
  simp only [miscOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h11
  obtain ⟨⟨⟨⟨⟨⟨⟨m1, m2⟩, m3⟩, m4⟩, m5⟩, m6⟩, m7⟩, m8⟩ := h11
  simp only [ttOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h10
  simp only [dtOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h9
  refine ⟨h1, h2, h3, h4, h5, h6, h7, m4, m5, m6, m7, qz_of_rows h8, ?_, ?_, ?_, m8⟩
  · intro c s hc hs
    obtain ⟨⟨a, b⟩, d⟩ := h9 c hc s hs
    exact ⟨entB_ent a, z4eq_eq b, z4eq_eq d⟩
  · refine ⟨h10.1, fun θ hθ => ?_⟩
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩ := h10.2 θ hθ
    exact ⟨entB_ent a1, entB_ent a2, entB_ent a3, z4eq_eq a4, z4eq_eq a5, z4eq_eq a6, z4eq_eq a7,
      z4eq_eq a8, z4eq_eq a9⟩
  · exact ⟨entB_ent m1, z4eq_eq m2, z4eq_eq m3⟩

end BeatAvg.K8
