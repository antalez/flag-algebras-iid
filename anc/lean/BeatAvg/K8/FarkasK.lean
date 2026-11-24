import BeatAvg.Cert.FarkasSound
import BeatAvg.K8.Atoms
import BeatAvg.K8.Excl

/-!
# Certificates of non-realizability in nested order
-/

open Finset

namespace BeatAvg.K8

open BeatAvg

theorem ordQ_mem_combos {n : ℕ} {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ ordQ n) : q ∈ Fast.combos n :=
  mem_combos.2 (mem_ordQ.1 hq)

theorem ordQ_getD_mem {n i : ℕ} (hi : i < (ordQ n).length) :
    (ordQ n).getD i (0, 0, 0, 0) ∈ ordQ n := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem pat_arr_getD (n : ℕ) (w : ℕ → ℝ) {i : ℕ} (hi : i < (ordQ n).length) :
    (pat n w).toArray.getD i 0 = trit w ((ordQ n).getD i (0, 0, 0, 0)) := by
  simp [pat, Array.getD, List.getD, hi]

/-- A valid certificate of non-realizability cannot be attached to the pattern of a sample. -/
theorem farkas_soundK {n : ℕ} {w : ℕ → ℝ} (hw : SG n w) (cert : Fast.Cert)
    (h : Fast.farkasOk (ordQ n) n (pat n w).toArray cert = true) : False := by
  simp only [Fast.farkasOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨hne, hall⟩, hsuf⟩ := h
  have hle := dot_nonpos hw (Fast.coefs (ordQ n) (pat n w).toArray cert) hsuf
  have hswap := swap_sum n w cert (fun e j => (e.2.2 : ℤ) *
    Fast.signOf e.2.1 ((pat n w).toArray.getD e.1 0) *
      Fast.coefE e.2.1 ((ordQ n).getD e.1 (0, 0, 0, 0)) j)
  have hcoefs : ∀ j, Fast.coefs (ordQ n) (pat n w).toArray cert j
      = (cert.map fun e => (e.2.2 : ℤ) * Fast.signOf e.2.1 ((pat n w).toArray.getD e.1 0) *
        Fast.coefE e.2.1 ((ordQ n).getD e.1 (0, 0, 0, 0)) j).sum := fun j => rfl
  simp only [hcoefs] at hle
  rw [hswap] at hle
  have hpos : 0 < (cert.map fun e => ((List.range n).map fun j =>
      (((e.2.2 : ℤ) * Fast.signOf e.2.1 ((pat n w).toArray.getD e.1 0) *
        Fast.coefE e.2.1 ((ordQ n).getD e.1 (0, 0, 0, 0)) j : ℤ) : ℝ) * w j).sum).sum := by
    refine list_sum_pos cert _ (by intro hc; simp [hc] at hne) fun e he => ?_
    obtain ⟨⟨hwt, hidx⟩, hkind⟩ := hall e he
    have hq := ordQ_mem_combos (ordQ_getD_mem hidx)
    have hinner : ((List.range n).map fun j =>
        (((e.2.2 : ℤ) * Fast.signOf e.2.1 ((pat n w).toArray.getD e.1 0) *
          Fast.coefE e.2.1 ((ordQ n).getD e.1 (0, 0, 0, 0)) j : ℤ) : ℝ) * w j).sum
        = (e.2.2 : ℝ) * ((Fast.signOf e.2.1 ((pat n w).toArray.getD e.1 0) : ℝ) *
          ((List.range n).map fun j =>
            (Fast.coefE e.2.1 ((ordQ n).getD e.1 (0, 0, 0, 0)) j : ℝ) * w j).sum) := by
      rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      push_cast
      ring
    rw [hinner, coefE_sum n w e.2.1 hq, pat_arr_getD n w hidx]
    exact mul_pos (by exact_mod_cast hwt) (entry_pos hw hq hkind)
  linarith

/-! ### Packed patterns -/

theorem unpackL_eq (N : ℕ) : ∀ (k p : ℕ), unpackL N k p = (List.range k).map fun i => tr N (p + i)
  | 0, _ => rfl
  | k + 1, p => by
    rw [unpackL, unpackL_eq N k (p + 1), List.range_succ_eq_map, List.map_cons, List.map_map]
    show _ :: _ = _ :: _
    congr 1
    refine List.map_congr_left fun a _ => ?_
    simp only [Function.comp_apply]
    congr 1
    omega

theorem unpackL_packL (xs : List ℕ) (hs : Small xs) : unpackL (packL xs) xs.length 0 = xs := by
  rw [unpackL_eq]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, zero_add, tr_packL _ _ hs,
      List.getD_eq_getElem _ _ h2]

theorem unpack_code (n : ℕ) (w : ℕ → ℝ) : unpackL (code n w) (ordQ n).length 0 = pat n w := by
  have h := unpackL_packL (pat n w) (pat_small n w)
  rwa [pat, List.length_map] at h

/-- A certificate attached to the code of a sample is not valid. -/
theorem exclK_false {n : ℕ} {w : ℕ → ℝ} (hw : SG n w) (c : ℕ) :
    exclK n (ordQ n).length (code n w) c = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [exclK, unpack_code] at h
  exact farkas_soundK hw _ h

end BeatAvg.K8
