import BeatAvg.Cert.QPsd
import BeatAvg.Five.Field

/-! The existing Gram and diagonal-dominance lemmas applied to the new blocks. -/
namespace BeatAvg.Five
open Fast.Five Finset

theorem dot_eq_dotL (a b : List ℤ) : dot a b = Fast.dotL a b := by
  induction a generalizing b with
  | nil => simp [dot, Fast.dotL]
  | cons x xs ih =>
    cases b with
    | nil => simp [dot, Fast.dotL]
    | cons y ys => simpa [dot, Fast.dotL] using congrArg (fun t => x*y+t) (ih ys)

theorem dot_comm (a b : List ℤ) : dot a b = dot b a := by
  induction a generalizing b with
  | nil => cases b <;> simp [dot]
  | cons x xs ih =>
    cases b with
    | nil => simp [dot]
    | cons y ys => simpa [dot, mul_comm] using congrArg (fun t => x*y+t) (ih ys)

theorem matrix_symmetric {lo hi : ℚ} {b : Block}
    (hp : ∀ i < b.matrix.size, psdRow lo hi b i = true)
    {i j : ℕ} (hi' : i < b.matrix.size) (hj : j < b.matrix.size) :
    entryAt b.matrix i j = entryAt b.matrix j i := by
  apply keq_sound
  have hh := hp i hi'
  simp only [psdRow, Bool.and_eq_true] at hh
  exact (List.all_eq_true.mp hh.1) j (List.mem_range.mpr hj)

theorem residual_symmetric {lo hi : ℚ} {b : Block}
    (hp : ∀ i < b.matrix.size, psdRow lo hi b i = true)
    {i j : ℕ} (hi' : i < b.matrix.size) (hj : j < b.matrix.size) :
    Fast.Five.residual b i j = Fast.Five.residual b j i := by
  unfold Fast.Five.residual
  rw [matrix_symmetric hp hi' hj, dot_comm]

theorem residual_row_bound {lo hi : ℚ} (he : EnclQ lo hi) {b : Block} {i : ℕ}
    (hp : psdRow lo hi b i = true) :
    ∑ j ∈ range b.matrix.size, (if j = i then 0 else |evalK (Fast.Five.residual b i j)|)
      ≤ evalK (Fast.Five.residual b i i) := by
  simp only [psdRow, Bool.and_eq_true, decide_eq_true_eq] at hp
  have h := hp.2
  have hcast := Rat.cast_le (K := ℝ).mpr h
  simp only [Rat.cast_list_sum, List.map_map, Function.comp_def] at hcast
  have heq : (((List.range b.matrix.size).map fun j =>
      ((if j = i then 0 else absBound lo hi (Fast.Five.residual b i j) : ℚ) : ℝ))).sum =
      ∑ j ∈ range b.matrix.size, (if j = i then 0 else (absBound lo hi (Fast.Five.residual b i j) : ℝ)) := by
    simp only [apply_ite, Rat.cast_zero]
    exact sum_map_range _ _
  rw [heq] at hcast
  refine le_trans (sum_le_sum fun j _ => ?_) (hcast.trans (lower_le he _))
  split_ifs
  · exact le_rfl
  · exact abs_le_bound he _

/-- Reduced matrix positivity: this reuses the old proof's diagonal-dominance
criterion and Gram identity, with the new (small) dimension. -/
theorem reduced_psd {lo hi : ℚ} (he : EnclQ lo hi) (b : Block)
    (hp : ∀ i < b.matrix.size, psdRow lo hi b i = true)
    (hg : ∀ i < b.matrix.size, (b.gram[i]?.getD []).length ≤ b.matrix.size)
    (u : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range b.matrix.size, ∑ j ∈ range b.matrix.size,
      u i * evalK (entryAt b.matrix i j) * u j := by
  let R := fun (i j : ℕ) => evalK (Fast.Five.residual b i j)
  let g := fun (k i : ℕ) => (((b.gram[i]?.getD []).getD k 0 : ℤ) : ℝ) / b.gramDen
  have hR : 0 ≤ ∑ i ∈ range b.matrix.size, ∑ j ∈ range b.matrix.size, u i * R i j * u j := by
    apply quad_nonneg_of_diag_dom
    intro i hi'
    have hs : ∀ j ∈ range b.matrix.size, R j i = R i j := by
      intro j hj
      exact congrArg evalK (residual_symmetric hp (mem_range.mp hj) (mem_range.mp hi'))
    apply le_trans (le_of_eq ?_) (residual_row_bound he (hp i (mem_range.mp hi')))
    apply sum_congr rfl
    intro j hj
    rw [hs j hj]
    split_ifs <;> ring
  have hG : 0 ≤ ∑ i ∈ range b.matrix.size, ∑ j ∈ range b.matrix.size,
      u i * (∑ k ∈ range b.matrix.size, g k i * g k j) * u j := by
    rw [gram_quad]
    exact sum_nonneg fun _ _ => sq_nonneg _
  have hy : ∀ i ∈ range b.matrix.size, ∀ j ∈ range b.matrix.size,
      evalK (entryAt b.matrix i j) = R i j + ∑ k ∈ range b.matrix.size, g k i * g k j := by
    intro i hi' j hj
    have hd := dotL_cast (b.gram[i]?.getD []) (b.gram[j]?.getD []) b.matrix.size
      (hg i (mem_range.mp hi'))
    simp only [R, Fast.Five.residual, evalK_sub, evalK_ofRat, Rat.cast_div, Rat.cast_intCast,
      Rat.cast_mul, Rat.cast_natCast, dot_eq_dotL, hd]
    simp only [g, div_mul_div_comm, ← sum_div]
    ring
  have hh : (∑ i ∈ range b.matrix.size, ∑ j ∈ range b.matrix.size,
      u i * evalK (entryAt b.matrix i j) * u j) =
      (∑ i ∈ range b.matrix.size, ∑ j ∈ range b.matrix.size, u i * R i j * u j) +
      ∑ i ∈ range b.matrix.size, ∑ j ∈ range b.matrix.size,
        u i * (∑ k ∈ range b.matrix.size, g k i * g k j) * u j := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi'
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    rw [hy i hi' j hj]
    ring
  rw [hh]
  exact add_nonneg hR hG

/-- Reuse the old sparse-matrix expansion lemma, at the new block size. -/
theorem expanded_dense (blk : Block)
    (hrow : ∀ (i : ℕ), ∀ (e : ℕ × Fast.K), e ∈ blk.basis[i]?.getD [] → e.1 < blk.matrix.size) (i j : ℕ) :
    evalK (expandedEntry blk i j) = ∑ a ∈ range blk.matrix.size, ∑ c ∈ range blk.matrix.size,
      Wd (blk.basis[i]?.getD []) a * evalK (entryAt blk.matrix a c) * Wd (blk.basis[j]?.getD []) c := by
  unfold expandedEntry
  change evalK (Fast.ksum _) = _
  rw [evalK_ksum, sum_map_flatMap]
  simp only [List.map_map]
  have h1 : ∀ e : ℕ × Fast.K, ((blk.basis[j]?.getD []).map (evalK ∘ fun e' =>
      (e.2.mul (entryAt blk.matrix e.1 e'.1)).mul e'.2)).sum
      = evalK e.2 * ∑ b ∈ range blk.matrix.size,
        evalK (entryAt blk.matrix e.1 b) * Wd (blk.basis[j]?.getD []) b := by
    intro e
    have h2 := sum_sparse blk.matrix.size (blk.basis[j]?.getD []) (hrow j)
      (fun b => evalK e.2 * evalK (entryAt blk.matrix e.1 b))
    rw [mul_sum]
    rw [show (∑ b ∈ range blk.matrix.size, evalK e.2 * (evalK (entryAt blk.matrix e.1 b)
        * Wd (blk.basis[j]?.getD []) b)) = ∑ b ∈ range blk.matrix.size, Wd (blk.basis[j]?.getD []) b
          * (evalK e.2 * evalK (entryAt blk.matrix e.1 b)) from
      sum_congr rfl fun b _ => by ring]
    rw [← h2]
    congr 1
    refine List.map_congr_left fun e' _ => ?_
    simp only [Function.comp_apply, evalK_mul]
    ring
  simp only [h1]
  have h3 := sum_sparse blk.matrix.size (blk.basis[i]?.getD []) (hrow i)
    (fun a => ∑ b ∈ range blk.matrix.size, evalK (entryAt blk.matrix a b) * Wd (blk.basis[j]?.getD []) b)
  rw [h3]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun b _ => by ring


/-- Positivity of W Y Wᵀ, including any zero flags used for unrecorded patterns. -/
theorem expanded_psd {lo hi : ℚ} (he : EnclQ lo hi) (blk : Block)
    (hp : ∀ i < blk.matrix.size, psdRow lo hi blk i = true)
    (hg : ∀ i < blk.matrix.size, (blk.gram[i]?.getD []).length ≤ blk.matrix.size)
    (hw : ∀ (i : ℕ), ∀ (e : ℕ × Fast.K), e ∈ blk.basis[i]?.getD [] → e.1 < blk.matrix.size)
    {M : ℕ} (v : Fin M → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * evalK (expandedEntry blk i.val j.val) * v j := by
  simp only [expanded_dense blk hw]
  rw [quad_congruence blk.matrix.size (fun i a => Wd (blk.basis[i.val]?.getD []) a)
    (fun a c => evalK (entryAt blk.matrix a c)) v]
  exact reduced_psd he blk hp hg fun a => ∑ i, v i * Wd (blk.basis[i.val]?.getD []) a

theorem shape_basis_bounds {b : Block} (hs : blockShape b = true) :
    ∀ (i : ℕ) (e : ℕ × Fast.K), e ∈ b.basis[i]?.getD [] → e.1 < b.matrix.size := by
  have hw : b.basis.all (fun row => row.all (fun e => decide (e.1 < b.matrix.size))) = true := by
    simp only [blockShape, Bool.and_eq_true] at hs
    tauto
  intro i e he
  by_cases hi : i < b.basis.size
  · have hh := Array.all_eq_true.mp hw i hi
    have hm : e ∈ b.basis[i] := by simpa [Array.getElem?_eq_getElem hi] using he
    exact of_decide_eq_true ((List.all_eq_true.mp hh) e hm)
  · simpa [Array.getElem?_eq_none (by omega : b.basis.size ≤ i)] using he

theorem shape_gram_bound {b : Block} (hs : blockShape b = true) :
    ∀ i < b.matrix.size, (b.gram[i]?.getD []).length ≤ b.matrix.size := by
  have hg : b.gram.all (fun row => row.length == b.matrix.size) = true := by
    simp only [blockShape, Bool.and_eq_true] at hs
    tauto
  intro i _
  by_cases hi : i < b.gram.size
  · have hh := Array.all_eq_true.mp hg i hi
    have he : b.gram[i].length = b.matrix.size := by simpa using hh
    simp [Array.getElem?_eq_getElem hi, he]
  · simp [Array.getElem?_eq_none (by omega : b.gram.size ≤ i)]

/-- Matrix positivity obtained directly from the two finite predicates. -/
theorem block_psd {lo hi : ℚ} (he : EnclQ lo hi) (b : Block)
    (hs : blockShape b = true)
    (hp : (List.range b.matrix.size).all (psdRow lo hi b) = true)
    {M : ℕ} (v : Fin M → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * evalK (expandedEntry b i.val j.val) * v j :=
  expanded_psd he b (fun i hi => (List.all_eq_true.mp hp) i (List.mem_range.mpr hi))
    (shape_gram_bound hs) (shape_basis_bounds hs) v

/-- The checked stored matrix agrees with W Y Wᵀ, including the zero default
row and column used for flags absent from the data. -/
theorem stored_eq_expanded {b : Block} (hs : blockShape b = true)
    (he : (List.range b.flags.size).all (expandedRow b) = true) (i j : ℕ) :
    entryAt b.expanded i j = expandedEntry b i j := by
  have hbs : b.basis.size = b.flags.size := by
    simp only [blockShape, Bool.and_eq_true, beq_iff_eq] at hs
    tauto
  have hes : b.expanded.size = b.flags.size := by
    simp only [blockShape, Bool.and_eq_true, beq_iff_eq] at hs
    tauto
  have her : b.expanded.all (fun row => row.size == b.flags.size) = true := by
    simp only [blockShape, Bool.and_eq_true] at hs
    tauto
  by_cases hi : i < b.flags.size
  · by_cases hj : j < b.flags.size
    · exact expanded_entry_sound ((List.all_eq_true.mp he) i (List.mem_range.mpr hi)) hj
    · have hi' : i < b.expanded.size := by omega
      have hr : b.expanded[i].size = b.flags.size := by
        simpa using Array.all_eq_true.mp her i hi'
      have hbj : b.basis[j]? = none := Array.getElem?_eq_none (by omega)
      have hej : b.expanded[i][j]? = none := Array.getElem?_eq_none (by omega)
      have hnil : (b.basis[i]?.getD []).flatMap (fun _ => ([] : List Fast.K)) = [] :=
        List.flatMap_eq_nil_iff.mpr (by simp)
      simp [entryAt, Array.getElem?_eq_getElem hi', hej, expandedEntry, hbj, ksum, hnil]
  · have hbi : b.basis[i]? = none := Array.getElem?_eq_none (by omega)
    have hei : b.expanded[i]? = none := Array.getElem?_eq_none (by omega)
    simp [entryAt, hei, expandedEntry, hbi, ksum]

end BeatAvg.Five
