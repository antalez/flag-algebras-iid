import BeatAvg.Cert.Idx7
import BeatAvg.Cert.GramBlock
import BeatAvg.Cert.PsdSound
import Fast.Cert7

/-!
# The order-7 flag certificate: families and their positive semidefiniteness
-/

open MeasureTheory Set Function Finset

namespace BeatAvg

/-- Family `k` of the order-7 certificate, with `t` roots and `m` further points. -/
noncomputable def fam7 (c7 : Fast.Cert7) (k t m : ℕ) : Fam 7 t m where
  eR := Fast.eR7 t
  eT := Fast.eT7 t m
  eT' := Fast.eT7' t m
  F := Fast.flag7 c7 k t m
  N := Fast.nFlags c7 k
  Q := fun i j => (Fast.QI c7 k i j : ℝ) / 4 ^ c7.scale

theorem dotI_cast (len : ℕ) (a b : Array ℤ) :
    ((Fast.dotI len a b : ℤ) : ℝ)
      = ∑ c ∈ range len, ((a.getD c 0 : ℤ) : ℝ) * ((b.getD c 0 : ℤ) : ℝ) := by
  unfold Fast.dotI
  rw [Int.cast_list_sum, List.map_map, ← sum_map_range]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply]
  push_cast
  rfl

theorem QI_cast (c7 : Fast.Cert7) (k i j : ℕ) :
    ((Fast.QI c7 k i j : ℤ) : ℝ)
      = if Fast.blk7 c7 k i = Fast.blk7 c7 k j then
          ∑ c ∈ range (c7.dims.getD k (0, 0, 0)).1,
            ((((c7.rows.getD k #[]).getD i #[]).getD c 0 : ℤ) : ℝ)
              * ((((c7.rows.getD k #[]).getD j #[]).getD c 0 : ℤ) : ℝ)
        else 0 := by
  unfold Fast.QI Fast.blk7
  split_ifs with h
  · exact dotI_cast _ _ _
  · simp

theorem fam7_psd (c7 : Fast.Cert7) (k t m : ℕ) (M : ℕ) (u : Fin M → ℝ) :
    0 ≤ ∑ i, ∑ j, u i * (fam7 c7 k t m).Q i.val j.val * u j := by
  have hb : ∀ i < M, Fast.blk7 c7 k i < (Finset.range M).sup (Fast.blk7 c7 k) + 1 := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := Fast.blk7 c7 k) (Finset.mem_range.2 hi))
  have hs4 : (0 : ℝ) < (4 : ℝ) ^ c7.scale := by positivity
  have hg := gram_block_psd M ((Finset.range M).sup (Fast.blk7 c7 k) + 1)
    (c7.dims.getD k (0, 0, 0)).1 (Fast.blk7 c7 k)
    (fun i c => ((((c7.rows.getD k #[]).getD i #[]).getD c 0 : ℤ) : ℝ)) hb u
  have e : ∑ i, ∑ j, u i * (fam7 c7 k t m).Q i.val j.val * u j
      = (∑ i : Fin M, ∑ j : Fin M,
          u i * (if Fast.blk7 c7 k i.val = Fast.blk7 c7 k j.val then
            ∑ c ∈ range (c7.dims.getD k (0, 0, 0)).1,
              ((((c7.rows.getD k #[]).getD i.val #[]).getD c 0 : ℤ) : ℝ)
                * ((((c7.rows.getD k #[]).getD j.val #[]).getD c 0 : ℤ) : ℝ)
            else 0) * u j) / (4 : ℝ) ^ c7.scale := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    show u i * ((Fast.QI c7 k i.val j.val : ℝ) / 4 ^ c7.scale) * u j = _
    rw [QI_cast]
    ring
  rw [e]
  exact div_nonneg hg hs4.le

theorem fam7_good (c7 : Fast.Cert7) (k t m : ℕ)
    (hinj : Injective (Sum.elim (Fast.eR7 t) (Sum.elim (Fast.eT7 t m) (Fast.eT7' t m)))) :
    (⟨t, m, fam7 c7 k t m⟩ : PFam 7).Good :=
  ⟨hinj, fam7_psd c7 k t m⟩

end BeatAvg
