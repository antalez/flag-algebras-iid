import BeatAvg.Six.Eval
import BeatAvg.Cert.SortedN
import BeatAvg.Cert.GramBlock
import BeatAvg.Cert.PsdMain

/-!
# The six-point flag certificate: soundness of the evaluation

If every pattern of a list that contains the patterns of all sorted samples passes `eval6`, then
`C ≤ lamP / lamQ`. This is `flag_bound` for the three families of the certificate.
-/

open MeasureTheory Set Function Finset

namespace BeatAvg.Six

/-! ### The index table -/

theorem idx6_spec : ∀ x y z d : Fin 6, x < y → y < z → z < d →
    (Fast.combos 6)[idx6 x.val y.val z.val d.val]? = some (x.val, y.val, z.val, d.val) := by
  decide

theorem idxOk6 : IdxOk 6 idx6 := by
  intro w x y z d hxy hyz hzd hd
  have h := idx6_spec ⟨x, by omega⟩ ⟨y, by omega⟩ ⟨z, by omega⟩ ⟨d, hd⟩ hxy hyz hzd
  simp only at h
  simp [patArr, h]

/-! ### The families -/

/-- A family of the certificate, with `t` roots and `m` further points. -/
noncomputable def fam (d : FamData) (cand : List (ℕ × ℕ × ℕ × ℕ)) (t m : ℕ) : Fam 6 t m where
  eR := eR6 t
  eT := eT6 t m
  eT' := eT6' t m
  F := flagIdx d cand t m
  N := d.keys.length
  Q := fun i j => (QI d i j : ℝ) / (D.den : ℝ)

theorem den_pos : (0 : ℝ) < (D.den : ℝ) := by
  have : (0 : ℤ) < D.den := by decide
  exact_mod_cast this

theorem rowOf_length_le (d : FamData) {LEN : ℕ} (h : ∀ r ∈ d.rows, r.length ≤ LEN) (i : ℕ) :
    (rowOf d i).length ≤ LEN := by
  unfold rowOf
  rw [List.length_map]
  by_cases hi : i < d.rows.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; simp

theorem QI_cast (d : FamData) {LEN : ℕ} (h : ∀ r ∈ d.rows, r.length ≤ LEN) (i j : ℕ) :
    ((QI d i j : ℤ) : ℝ)
      = if d.blk.getD i 0 = d.blk.getD j 0 then
          ∑ c ∈ range LEN, (((rowOf d i).getD c 0 : ℤ) : ℝ) * (((rowOf d j).getD c 0 : ℤ) : ℝ)
        else 0 := by
  unfold QI
  split_ifs with hb
  · exact dotL_cast _ _ LEN (rowOf_length_le d h i)
  · simp

/-- The quadratic form of a family is positive semidefinite, in every size. -/
theorem fam_psd (d : FamData) (cand : List (ℕ × ℕ × ℕ × ℕ)) (t m : ℕ) {LEN : ℕ}
    (h : ∀ r ∈ d.rows, r.length ≤ LEN) (M : ℕ) (u : Fin M → ℝ) :
    0 ≤ ∑ i, ∑ j, u i * (fam d cand t m).Q i.val j.val * u j := by
  have hb : ∀ i < M, d.blk.getD i 0 < (Finset.range M).sup (fun i => d.blk.getD i 0) + 1 :=
    fun i hi => Nat.lt_succ_of_le
      (Finset.le_sup (f := fun i => d.blk.getD i 0) (Finset.mem_range.2 hi))
  have hg := gram_block_psd M ((Finset.range M).sup (fun i => d.blk.getD i 0) + 1) LEN
    (fun i => d.blk.getD i 0) (fun i c => (((rowOf d i).getD c 0 : ℤ) : ℝ)) hb u
  have e : ∑ i, ∑ j, u i * (fam d cand t m).Q i.val j.val * u j
      = (∑ i : Fin M, ∑ j : Fin M,
          u i * (if d.blk.getD i.val 0 = d.blk.getD j.val 0 then
            ∑ c ∈ range LEN, (((rowOf d i.val).getD c 0 : ℤ) : ℝ)
              * (((rowOf d j.val).getD c 0 : ℤ) : ℝ)
            else 0) * u j) / (D.den : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    show u i * ((QI d i.val j.val : ℝ) / (D.den : ℝ)) * u j = _
    rw [QI_cast d h]
    ring
  rw [e]
  exact div_nonneg hg den_pos.le

theorem lenA : ∀ r ∈ famA.rows, r.length ≤ 63 := by decide
theorem lenB : ∀ r ∈ famB.rows, r.length ≤ 63 := by decide
theorem lenC : ∀ r ∈ famC.rows, r.length ≤ 63 := by decide +kernel

theorem inj22 : Injective (Sum.elim (eR6 2) (Sum.elim (eT6 2 2) (eT6' 2 2))) := by decide
theorem inj31 : Injective (Sum.elim (eR6 3) (Sum.elim (eT6 3 1) (eT6' 3 1))) := by decide
theorem inj41 : Injective (Sum.elim (eR6 4) (Sum.elim (eT6 4 1) (eT6' 4 1))) := by decide
theorem e46_inj : Injective e46 := by decide

/-- The three families of the certificate. -/
noncomputable def fams6 : List (PFam 6) :=
  [⟨2, 2, fam famA cand4 2 2⟩, ⟨3, 1, fam famB cand4 3 1⟩, ⟨4, 1, fam famC cand5 4 1⟩]

theorem fams6_good : ∀ f ∈ fams6, f.Good := by
  intro f hf
  simp only [fams6, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨inj22, fam_psd famA cand4 2 2 lenA⟩
  · exact ⟨inj31, fam_psd famB cand4 3 1 lenB⟩
  · exact ⟨inj41, fam_psd famC cand5 4 1 lenC⟩

/-! ### The lists of arrangements -/

theorem fnOf6_inj {l l' : List (Fin 6)} (h : l.length = 6) (h' : l'.length = 6)
    (e : fnOf6 l = fnOf6 l') : l = l' := by
  apply List.ext_getElem (by rw [h, h'])
  intro i h1 h2
  have := congrFun e ⟨i, by omega⟩
  simpa [fnOf6, List.getD, h1, h2] using this

/-- The facts about a list of arrangements with `t` roots and twice `m` further points. -/
structure RepFacts (t m : ℕ) (reps : List (List (Fin 6))) : Prop where
  nodup : reps.Nodup
  count : reps.length * (t.factorial * m.factorial * m.factorial) = Nat.factorial 6
  good : ∀ l ∈ reps, l.length = 6 ∧ Injective (fnOf6 l) ∧
    Injective (fnOf6 l ∘ Fast.appendF (eR6 t) (eT6 t m)) ∧
    Injective (fnOf6 l ∘ Fast.appendF (eR6 t) (eT6' t m)) ∧
    (∀ i j : Fin t, i < j → fnOf6 l (eR6 t i) < fnOf6 l (eR6 t j)) ∧
    (∀ i j : Fin m, i < j → fnOf6 l (eT6 t m i) < fnOf6 l (eT6 t m j)) ∧
    (∀ i j : Fin m, i < j → fnOf6 l (eT6' t m i) < fnOf6 l (eT6' t m j))

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem factsA : RepFacts 2 2 repsA := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem factsB : RepFacts 3 1 repsB := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem factsC : RepFacts 4 1 repsC := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The two blocks of the objective term: the three summands and the two unused points. -/
def embO1 : Fin 3 ↪ Fin 6 := ⟨fun i => e46 i.castSucc, by decide⟩
def embO2 : Fin 2 ↪ Fin 6 := ⟨fun i => Fin.ofNat 6 (4 + i.val), by decide⟩

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem objFacts : repsO.Nodup ∧ repsO.length = 60 ∧
    ∀ l ∈ repsO, l.length = 6 ∧ Injective (fnOf6 l) ∧
      (∀ i j : Fin 3, i < j → fnOf6 l (embO1 i) < fnOf6 l (embO1 j)) ∧
      (∀ i j : Fin 2, i < j → fnOf6 l (embO2 i) < fnOf6 l (embO2 j)) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ### The functional of a sorted sample -/

theorem sum_map_div' {α : Type*} (l : List α) (g : α → ℝ) (d : ℝ) :
    (l.map fun a => g a / d).sum = (l.map g).sum / d := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_map_countP {α : Type*} (l : List α) (p : α → Bool) :
    (l.map fun a => if p a then (1 : ℝ) else 0).sum = (l.countP p : ℝ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih] <;> ring

/-- The sum of a square term over all orderings of a sorted sample. -/
theorem fam_sum (d : FamData) (cand : List (ℕ × ℕ × ℕ × ℕ)) {t m : ℕ}
    {reps : List (List (Fin 6))} (F : RepFacts t m reps)
    (hinj : Injective (Sum.elim (eR6 t) (Sum.elim (eT6 t m) (eT6' t m))))
    {ω : Fin 6 → ℝ} (hω : SGn 6 ω) :
    ∑ π : Equiv.Perm (Fin 6), (fam d cand t m).term (ω ∘ ⇑π)
      = ((t.factorial * m.factorial * m.factorial : ℕ) : ℝ)
        * ((famSum d cand t m reps (cfgOf ω) : ℤ) : ℝ) / (D.den : ℝ) := by
  have h := (fam d cand t m).sum_perm hinj fnOf6 reps F.nodup
    (fun l hl l' hl' e => fnOf6_inj (F.good l hl).1 (F.good l' hl').1 e)
    (fun l hl => by
      obtain ⟨-, h0, h1, h2, h3, h4, h5⟩ := F.good l hl
      exact ⟨h0, h1, h2, fun i j hij => h3 i j hij, fun i j hij => h4 i j hij,
        fun i j hij => h5 i j hij⟩)
    F.count hω.mono.monotone
  rw [h]
  have e : (reps.map fun l => (fam d cand t m).Q
      ((fam d cand t m).F ((cfgOf ω).comap (fnOf6 l ∘ Fast.appendF (fam d cand t m).eR
        (fam d cand t m).eT)) % (fam d cand t m).N)
      ((fam d cand t m).F ((cfgOf ω).comap (fnOf6 l ∘ Fast.appendF (fam d cand t m).eR
        (fam d cand t m).eT')) % (fam d cand t m).N)).sum
      = ((famSum d cand t m reps (cfgOf ω) : ℤ) : ℝ) / (D.den : ℝ) := by
    unfold famSum
    rw [Int.cast_list_sum, List.map_map, ← sum_map_div']
    rfl
  rw [e]
  ring

theorem obj_sum (ω : Fin 6 → ℝ) :
    ∑ π : Equiv.Perm (Fin 6), objG e46 (ω ∘ ⇑π) = 12 * (objCount (cfgOf ω) : ℝ) := by
  obtain ⟨hnd, hlen, hgood⟩ := objFacts
  have h := objG_sum_perm e46 e46_inj embO1 (fun _ => rfl) embO2 (by decide) fnOf6
    repsO hnd
    (fun l hl l' hl' e => fnOf6_inj (hgood l hl).1 (hgood l' hl').1 e)
    (fun l hl => by
      obtain ⟨-, h0, g1, g2⟩ := hgood l hl
      exact ⟨h0, fun i j hij => g1 i j hij, fun i j hij => g2 i j hij⟩)
    (by rw [hlen]; decide) ω
  have hK : ((Nat.factorial 3 * Nat.factorial 2 * Nat.factorial 0 : ℕ) : ℝ) = 12 := by
    norm_num [Nat.factorial]
  rw [h, hK]
  congr 1
  unfold objCount
  exact sum_map_countP repsO fun l =>
    (cfgOf ω).sb (fnOf6 l (e46 0)) (fnOf6 l (e46 1)) (fnOf6 l (e46 2)) (fnOf6 l (e46 3))

/-- On a sorted sample, `6! · den · Λ` is the integer computed by the checker. -/
theorem LamF6_sorted {ω : Fin 6 → ℝ} (hω : SGn 6 ω) :
    LamF e46 fams6 ω = ((total6 (cfgOf ω) : ℤ) : ℝ) / (720 * (D.den : ℝ)) := by
  have hd := den_pos
  have f6 : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
  have k22 : ((Nat.factorial 2 * Nat.factorial 2 * Nat.factorial 2 : ℕ) : ℝ) = 8 := by
    norm_num [Nat.factorial]
  have k31 : ((Nat.factorial 3 * Nat.factorial 1 * Nat.factorial 1 : ℕ) : ℝ) = 6 := by
    norm_num [Nat.factorial]
  have k41 : ((Nat.factorial 4 * Nat.factorial 1 * Nat.factorial 1 : ℕ) : ℝ) = 24 := by
    norm_num [Nat.factorial]
  unfold LamF
  simp only [lamF, fams6, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sum_add_distrib, add_zero]
  rw [obj_sum ω, fam_sum famA cand4 factsA inj22 hω, fam_sum famB cand4 factsB inj31 hω,
    fam_sum famC cand5 factsC inj41 hω, f6, k22, k31, k41]
  unfold total6
  push_cast
  field_simp
  ring

/-- A pattern accepted by the checker bounds the functional on the corresponding samples. -/
theorem eval6_sound {ω : Fin 6 → ℝ} (hω : SGn 6 ω)
    (h : eval6 ((Fast.combos 6).map (trit (extNn ω))) = true) :
    LamF e46 fams6 ω ≤ (D.lamP : ℝ) / (D.lamQ : ℝ) := by
  have hc : cfgOf ω = cfg6 (patArr 6 (extNn ω)) := cfgOf_eq_patG (n := 6) (by norm_num) idxOk6 hω
  unfold eval6 at h
  have h1 : total6 (cfg6 (patArr 6 (extNn ω))) * D.lamQ ≤ 720 * D.den * D.lamP :=
    of_decide_eq_true h
  rw [← hc] at h1
  have h2 : ((total6 (cfgOf ω) : ℤ) : ℝ) * (D.lamQ : ℝ) ≤ 720 * (D.den : ℝ) * (D.lamP : ℝ) := by
    exact_mod_cast h1
  have hq : (0 : ℝ) < (D.lamQ : ℝ) := by
    have : (0 : ℤ) < D.lamQ := by decide
    exact_mod_cast this
  have hs : (0 : ℝ) < 720 * (D.den : ℝ) := by have := den_pos; positivity
  rw [LamF6_sorted hω, div_le_div_iff₀ hs hq]
  linarith

/-- **The six-point flag bound**, given the two finite facts: the list `L6` contains the pattern
of every sorted sample in general position, and all its patterns pass the check. -/
theorem C_le_of_checks
    (hcov : ∀ w : ℕ → ℝ, SG 6 w → (Fast.combos 6).map (trit w) ∈ D.L6)
    (hall : ∀ v ∈ D.L6, eval6 v = true) : C ≤ (D.lamP : ℝ) / (D.lamQ : ℝ) :=
  flag_bound e46 e46_inj fams6 fams6_good _
    (LamF_le_of_sorted _ _ _ fun ω hω =>
      eval6_sound hω (hall _ (hcov _ (SG_extNn (by norm_num) hω))))

end BeatAvg.Six
