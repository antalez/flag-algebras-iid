import BeatAvg.Cert.PsdMain

/-!
# `Q = W Y W^T` is positive semidefinite
-/

open Finset

namespace BeatAvg

theorem evalK_foldl (l : List Fast.K) (acc : Fast.K) :
    evalK (l.foldl Fast.K.add acc) = evalK acc + (l.map evalK).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, ih, evalK_add, List.map_cons, List.sum_cons]; ring

theorem evalK_ksum (l : List Fast.K) : evalK (Fast.ksum l) = (l.map evalK).sum := by
  unfold Fast.ksum
  rw [evalK_foldl, evalK_zero, zero_add]

theorem sum_map_flatMap {α β : Type*} (l : List α) (f : α → List β) (g : β → ℝ) :
    ((l.flatMap f).map g).sum = (l.map fun e => ((f e).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- Dense entry of a sparse row. -/
noncomputable def Wd (l : List (ℕ × Fast.K)) (a : ℕ) : ℝ :=
  (l.map fun e => if e.1 = a then evalK e.2 else 0).sum

theorem sum_sparse (n : ℕ) (l : List (ℕ × Fast.K)) (hl : ∀ e ∈ l, e.1 < n) (G : ℕ → ℝ) :
    (l.map fun e => evalK e.2 * G e.1).sum = ∑ a ∈ range n, Wd l a * G a := by
  induction l with
  | nil => simp [Wd]
  | cons e l ih =>
    have he : e.1 < n := hl e List.mem_cons_self
    have ih' := ih fun e' he' => hl e' (List.mem_cons_of_mem _ he')
    have hW : ∀ a, Wd (e :: l) a = (if e.1 = a then evalK e.2 else 0) + Wd l a := by
      intro a; simp [Wd]
    simp only [List.map_cons, List.sum_cons, ih', hW, add_mul, sum_add_distrib]
    congr 1
    rw [sum_congr rfl fun a _ => ite_mul (e.1 = a) (evalK e.2) 0 (G a)]
    simp only [zero_mul]
    rw [sum_ite_eq (range n) e.1 (fun a => evalK e.2 * G a), if_pos (mem_range.2 he)]

theorem QK_dense (c : Fast.Cert8) (hW : Fast.wOk c = true) (i j : ℕ) :
    evalK (Fast.QK c i j) = ∑ a ∈ range 255, ∑ b ∈ range 255,
      Wd (c.W.getD i []) a * evalK (Fast.yAt c.Yr a b) * Wd (c.W.getD j []) b := by
  have hrow : ∀ k, ∀ e ∈ c.W.getD k [], e.1 < 255 := by
    intro k e he
    unfold Fast.wOk at hW
    rw [List.all_eq_true] at hW
    by_cases hk : k < c.W.size
    · have hmem : c.W.getD k [] ∈ c.W.toList := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
        simp
      have := List.all_eq_true.1 (hW _ hmem) e he
      simpa using this
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at he
      simp at he
  unfold Fast.QK Fast.QKw
  rw [evalK_ksum, sum_map_flatMap]
  simp only [List.map_map]
  have h1 : ∀ e : ℕ × Fast.K, ((c.W.getD j []).map (evalK ∘ fun e' =>
      (e.2.mul (Fast.yAt c.Yr e.1 e'.1)).mul e'.2)).sum
      = evalK e.2 * ∑ b ∈ range 255,
        evalK (Fast.yAt c.Yr e.1 b) * Wd (c.W.getD j []) b := by
    intro e
    have h2 := sum_sparse 255 (c.W.getD j []) (hrow j)
      (fun b => evalK e.2 * evalK (Fast.yAt c.Yr e.1 b))
    rw [mul_sum]
    rw [show (∑ b ∈ range 255, evalK e.2 * (evalK (Fast.yAt c.Yr e.1 b)
        * Wd (c.W.getD j []) b)) = ∑ b ∈ range 255, Wd (c.W.getD j []) b
          * (evalK e.2 * evalK (Fast.yAt c.Yr e.1 b)) from
      sum_congr rfl fun b _ => by ring]
    rw [← h2]
    congr 1
    refine List.map_congr_left fun e' _ => ?_
    simp only [Function.comp_apply, evalK_mul]
    ring
  simp only [h1]
  have h3 := sum_sparse 255 (c.W.getD i []) (hrow i)
    (fun a => ∑ b ∈ range 255, evalK (Fast.yAt c.Yr a b) * Wd (c.W.getD j []) b)
  rw [h3]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun b _ => by ring

end BeatAvg

namespace BeatAvg

open Finset

theorem quad_congruence {ι : Type*} [Fintype ι] (n : ℕ) (Wm : ι → ℕ → ℝ) (Y : ℕ → ℕ → ℝ)
    (v : ι → ℝ) :
    ∑ i, ∑ j, v i * (∑ a ∈ range n, ∑ b ∈ range n, Wm i a * Y a b * Wm j b) * v j
      = ∑ a ∈ range n, ∑ b ∈ range n, (∑ i, v i * Wm i a) * Y a b * (∑ j, v j * Wm j b) := by
  have hR : ∀ a b, (∑ i, v i * Wm i a) * Y a b * (∑ j, v j * Wm j b)
      = ∑ i, ∑ j, v i * (Wm i a * Y a b * Wm j b) * v j := by
    intro a b
    rw [sum_mul, sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    ring
  simp only [hR]
  calc ∑ i, ∑ j, v i * (∑ a ∈ range n, ∑ b ∈ range n, Wm i a * Y a b * Wm j b) * v j
      = ∑ i, ∑ j, ∑ a ∈ range n, ∑ b ∈ range n, v i * (Wm i a * Y a b * Wm j b) * v j := by
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum, sum_mul]
    _ = ∑ i, ∑ a ∈ range n, ∑ j, ∑ b ∈ range n, v i * (Wm i a * Y a b * Wm j b) * v j :=
        sum_congr rfl fun i _ => sum_comm
    _ = ∑ a ∈ range n, ∑ i, ∑ j, ∑ b ∈ range n, v i * (Wm i a * Y a b * Wm j b) * v j := sum_comm
    _ = ∑ a ∈ range n, ∑ i, ∑ b ∈ range n, ∑ j, v i * (Wm i a * Y a b * Wm j b) * v j :=
        sum_congr rfl fun a _ => sum_congr rfl fun i _ => sum_comm
    _ = ∑ a ∈ range n, ∑ b ∈ range n, ∑ i, ∑ j, v i * (Wm i a * Y a b * Wm j b) * v j :=
        sum_congr rfl fun a _ => sum_comm

/-- `Q = W Y W^T` is positive semidefinite. -/
theorem Q_psd (c : Fast.Cert8) (he : Encl c.encLo c.encHi c.encM) (hpsd : Fast.psdOk c = true)
    (hW : Fast.wOk c = true) (v : Fin 300 → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * evalK (Fast.QK c i.val j.val) * v j := by
  simp only [QK_dense c hW]
  rw [quad_congruence 255 (fun i a => Wd (c.W.getD i.val []) a)
    (fun a b => evalK (Fast.yAt c.Yr a b)) v]
  exact Y_psd c he hpsd fun a => ∑ i, v i * Wd (c.W.getD i.val []) a

end BeatAvg
