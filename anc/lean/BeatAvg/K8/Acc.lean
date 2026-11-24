import BeatAvg.Cert.KReal
import BeatAvg.K8.Fields
import BeatAvg.K8.Eval

/-!
# The accumulators of the evaluation as sums of lists of entries
-/

namespace BeatAvg.K8

open BeatAvg
open Fast (Z4)

theorem sqAcc_eq (t : Tb) (C : ℕ) : ∀ (l : List (ℕ × ℕ × ℕ × ℕ)) (acc : ℕ),
    sqAcc t C l acc = acc + (l.map (sqEnt t C)).sum
  | [], acc => by simp [sqAcc]
  | e :: l, acc => by
    rw [sqAcc, sqAcc_eq t C l, List.map_cons, List.sum_cons, nadd]
    ring

theorem degAcc_eq (t : Tb) (N C : ℕ) : ∀ (l : List (ℕ × ℕ × ℕ × ℕ)) (acc : ℕ),
    degAcc t N C l acc = acc + (l.map (degEnt t N C)).sum
  | [], acc => by simp [degAcc]
  | e :: l, acc => by
    rw [degAcc, degAcc_eq t N C l, List.map_cons, List.sum_cons, nadd]
    ring

/-- The condition "no forbidden bit is hot". -/
def clr (H f : ℕ) : Bool := Nat.beq (Nat.land H f) 0

theorem clr_iff (H f : ℕ) : clr H f = true ↔ Nat.land H f = 0 := by
  simp [clr]

theorem sel_eq (H f x z : ℕ) : sel H f x z = bif clr H f then x else z := rfl

theorem objCnt_eq (H : ℕ) : ∀ (l : List ℕ) (acc : ℕ), objCnt H l acc = acc + l.countP (clr H)
  | [], acc => by simp [objCnt]
  | f :: l, acc => by
    rw [objCnt, objCnt_eq H l, sel_eq, List.countP_cons]
    cases clr H f <;> simp <;> ring

/-- The entries added for one arrangement with roots of type 0. -/
def thrL (H z : ℕ) : List (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ) → List ℕ
  | f :: fs, e :: es =>
    sel H f.1 e.1 z :: sel H f.2.1 e.2.1 z :: sel H f.2.2 e.2.2 z :: thrL H z fs es
  | _, _ => []

theorem thrTh_eq (H z : ℕ) : ∀ (fs es : List (ℕ × ℕ × ℕ)) (acc : ℕ),
    thrTh H z fs es acc = acc + (thrL H z fs es).sum
  | [], _, acc => by simp [thrTh, thrL]
  | _ :: _, [], acc => by simp [thrTh, thrL]
  | f :: fs, e :: es, acc => by
    rw [thrTh, thrTh_eq H z fs es, thrL]
    simp only [List.sum_cons, nadd]
    ring

/-- The 24 entries added for one arrangement. -/
def thrEnts (H z : ℕ) (TT : List (ℕ × ℕ × ℕ)) (e : ℕ × List (ℕ × ℕ × ℕ)) : List ℕ :=
  bif clr H e.1 then thrL H z e.2 TT else List.replicate 24 z

theorem thrAcc_eq (t : Tb) (H z : ℕ) : ∀ (l : List (ℕ × List (ℕ × ℕ × ℕ))) (acc : ℕ),
    thrAcc t H z (Nat.mul 24 z) l acc = acc + (l.flatMap (thrEnts H z t.TT)).sum
  | [], acc => by simp [thrAcc]
  | e :: l, acc => by
    have hc : Nat.beq (Nat.land H e.1) 0 = clr H e.1 := rfl
    rw [thrAcc, thrAcc_eq t H z l, List.flatMap_cons, List.sum_append, hc]
    simp only [thrEnts]
    cases clr H e.1
    · simp only [Bool.cond_false, nadd, nmul, List.sum_replicate, smul_eq_mul]
      ring
    · simp only [Bool.cond_true, thrTh_eq]
      ring

/-! ### Decoding -/

/-- The element of `Z[r]` in the fields `k, .., k + 3` of an entry. -/
def entZ (w off E k : ℕ) : Z4 :=
  ⟨(fieldAt w E k : ℤ) - off, (fieldAt w E (k + 1) : ℤ) - off, (fieldAt w E (k + 2) : ℤ) - off,
    (fieldAt w E (k + 3) : ℤ) - off⟩

/-- A field minus the offset, as a real number. -/
noncomputable def fz (w off e j : ℕ) : ℝ := (fieldAt w e j : ℝ) - (off : ℝ)

theorem evalZ_entZ (w off e k : ℕ) :
    evalZ (entZ w off e k)
      = fz w off e k + fz w off e (k + 1) * rr + fz w off e (k + 2) * rr ^ 2
        + fz w off e (k + 3) * rr ^ 3 := by
  simp only [evalZ, entZ, fz]
  push_cast
  ring

theorem sum_sub_const (es : List ℕ) (f : ℕ → ℕ) (c : ℕ) :
    (((es.map f).sum : ℕ) : ℝ) - ((es.length * c : ℕ) : ℝ)
      = (es.map fun e => (f e : ℝ) - (c : ℝ)).sum := by
  induction es with
  | nil => simp
  | cons a es ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [← ih]
    push_cast
    ring

theorem fld_cast (acc w j o : ℕ) :
    ((fld acc w j o : ℤ) : ℝ) = (fieldAt w acc j : ℝ) - (o : ℝ) := by
  have : fld acc w j o = ((fieldAt w acc j : ℕ) : ℤ) - ((o : ℕ) : ℤ) := rfl
  rw [this]
  push_cast
  ring

/-- The fields of a sum of entries, decoded, are the sum of the decoded entries. -/
theorem evalZ_decZ {w w0 K : ℕ} (es : List ℕ) (off k n : ℕ) (hE : ∀ e ∈ es, Ent w w0 K e)
    (hlen : es.length * 2 ^ w0 ≤ 2 ^ w) (hk : k + 3 < K) (hn : n = es.length) :
    evalZ (decZ es.sum w k (Nat.mul n off)) = (es.map fun e => evalZ (entZ w off e k)).sum := by
  subst hn
  have hs := (fields_sum es hE hlen).2
  have key : ∀ j, j < K → ((fld es.sum w j (Nat.mul es.length off) : ℤ) : ℝ)
      = (es.map fun e => fz w off e j).sum := by
    intro j hj
    rw [fld_cast, hs j hj]
    exact sum_sub_const es (fun e => fieldAt w e j) off
  have h0 := key k (by omega)
  have h1 := key (k + 1) (by omega)
  have h2 := key (k + 2) (by omega)
  have h3 := key (k + 3) (by omega)
  have hf : (fun e => evalZ (entZ w off e k)) = fun e =>
      fz w off e k + fz w off e (k + 1) * rr + fz w off e (k + 2) * rr ^ 2
        + fz w off e (k + 3) * rr ^ 3 := funext fun e => evalZ_entZ w off e k
  rw [hf, List.sum_map_add, List.sum_map_add, List.sum_map_add, List.sum_map_mul_right,
    List.sum_map_mul_right, List.sum_map_mul_right, ← h0, ← h1, ← h2, ← h3]
  rfl

end BeatAvg.K8
