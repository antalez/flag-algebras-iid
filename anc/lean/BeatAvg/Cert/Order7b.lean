import BeatAvg.Cert.Order7
import BeatAvg.Cert.EvalZ

/-!
# The order-7 certificate on sorted samples
-/

open MeasureTheory Set Function Finset

namespace BeatAvg

/-- The five families of the order-7 certificate. -/
noncomputable def fams7 (c7 : Fast.Cert7) : List (PFam 7) :=
  [⟨1, 3, fam7 c7 0 1 3⟩, ⟨2, 2, fam7 c7 1 2 2⟩, ⟨3, 2, fam7 c7 2 3 2⟩, ⟨4, 1, fam7 c7 3 4 1⟩,
    ⟨5, 1, fam7 c7 4 5 1⟩]

theorem fams7_good (c7 : Fast.Cert7) : ∀ f ∈ fams7 c7, f.Good := by
  intro f hf
  simp only [fams7, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact fam7_good c7 0 1 3 facts14.inj
  · exact fam7_good c7 1 2 2 facts24.inj
  · exact fam7_good c7 2 3 2 facts35.inj
  · exact fam7_good c7 3 4 1 facts45.inj
  · exact fam7_good c7 4 5 1 facts56.inj

theorem sum_map_div {α : Type*} (l : List α) (g : α → ℝ) (d : ℝ) :
    (l.map fun a => g a / d).sum = (l.map g).sum / d := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- The sum of a square term over all orderings of a sorted sample. -/
theorem fam7_sum (c7 : Fast.Cert7) (k : ℕ) {t m : ℕ} {reps : List (List (Fin 7))} {fib : ℕ}
    (F : FamFacts t m reps fib) {ω : Fin 7 → ℝ} (hω : SGn 7 ω) :
    ∑ π : Equiv.Perm (Fin 7), (fam7 c7 k t m).term (ω ∘ ⇑π)
      = fib * ((Fast.famSum c7 k t m reps (cfgOf ω) : ℤ) : ℝ) / 4 ^ c7.scale := by
  have h := (fam7 c7 k t m).sum_perm F.inj Fast.fnOf7 reps F.nodup
    (fun l hl l' hl' e => fnOf7_inj (F.good l hl).1 (F.good l' hl').1 e)
    (fun l hl => by
      obtain ⟨-, h0, h1, h2, h3, h4, h5⟩ := F.good l hl
      exact ⟨h0, h1, h2, fun i j hij => h3 i j hij, fun i j hij => h4 i j hij,
        fun i j hij => h5 i j hij⟩)
    (by rw [← F.kfac, F.count]; decide)
    hω.mono.monotone
  rw [h, ← F.kfac]
  have e : (reps.map fun l => (fam7 c7 k t m).Q
      ((fam7 c7 k t m).F ((cfgOf ω).comap (Fast.fnOf7 l ∘ Fast.appendF (fam7 c7 k t m).eR
        (fam7 c7 k t m).eT)) % (fam7 c7 k t m).N)
      ((fam7 c7 k t m).F ((cfgOf ω).comap (Fast.fnOf7 l ∘ Fast.appendF (fam7 c7 k t m).eR
        (fam7 c7 k t m).eT')) % (fam7 c7 k t m).N)).sum
      = ((Fast.famSum c7 k t m reps (cfgOf ω) : ℤ) : ℝ) / 4 ^ c7.scale := by
    unfold Fast.famSum
    rw [Int.cast_list_sum, List.map_map, ← sum_map_div]
    rfl
  rw [e]
  ring

theorem obj7_sum (ω : Fin 7 → ℝ) :
    ∑ π : Equiv.Perm (Fin 7), objG Fast.e47 (ω ∘ ⇑π) = 36 * (Fast.objCount7 (cfgOf ω) : ℝ) := by
  have h := objG_sum_perm Fast.e47 e47_inj embO1 (fun _ => rfl) embO2 (by decide) Fast.fnOf7
    Fast.repsObj7 obj7_nodup
    (fun l hl l' hl' e => fnOf7_inj (obj7_good l hl).1 (obj7_good l' hl').1 e)
    (fun l hl => by
      obtain ⟨-, h0, g1, g2⟩ := obj7_good l hl
      exact ⟨h0, fun i j hij => g1 i j hij, fun i j hij => g2 i j hij⟩)
    (by rw [obj7_length]; decide) ω
  have hK : ((Nat.factorial 3 * Nat.factorial 3 * Nat.factorial 0 : ℕ) : ℝ) = 36 := by
    norm_num [Nat.factorial]
  rw [h, hK]
  congr 1
  unfold Fast.objCount7
  exact sum_map_ite_countP Fast.repsObj7 fun l =>
    (cfgOf ω).sb (Fast.fnOf7 l (Fast.e47 0)) (Fast.fnOf7 l (Fast.e47 1))
      (Fast.fnOf7 l (Fast.e47 2)) (Fast.fnOf7 l (Fast.e47 3))

theorem fact7 : (Nat.factorial 7 : ℝ) = 5040 := by norm_num [Nat.factorial]

/-- On a sorted sample, `7! · 4^scale · Λ` is the integer computed by the checker. -/
theorem LamF7_sorted (c7 : Fast.Cert7) {ω : Fin 7 → ℝ} (hω : SGn 7 ω) :
    LamF Fast.e47 (fams7 c7) ω
      = ((Fast.total7 c7 (cfgOf ω) : ℤ) : ℝ) / (5040 * 4 ^ c7.scale) := by
  have hs4 : (4 : ℝ) ^ c7.scale ≠ 0 := by positivity
  unfold LamF
  simp only [lamF, fams7, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sum_add_distrib, add_zero]
  rw [obj7_sum ω, fam7_sum c7 0 facts14 hω, fam7_sum c7 1 facts24 hω, fam7_sum c7 2 facts35 hω,
    fam7_sum c7 3 facts45 hω, fam7_sum c7 4 facts56 hω, fact7]
  unfold Fast.total7
  push_cast
  field_simp
  ring

/-- A pattern accepted by the checker bounds the functional on the corresponding samples. -/
theorem eval7_sound (c7 : Fast.Cert7) {ω : Fin 7 → ℝ} (hω : SGn 7 ω)
    (h : Fast.eval7 c7 (patArr 7 (extNn ω)) = true) :
    LamF Fast.e47 (fams7 c7) ω ≤ 801509 / 2000000 := by
  have hc := cfgOf_eq_patG (n := 7) (by norm_num) idxOk7 hω
  unfold Fast.eval7 at h
  rw [← hc] at h
  have h1 : 2000000 * Fast.total7 c7 (cfgOf ω) ≤ 5040 * 4 ^ c7.scale * 801509 :=
    of_decide_eq_true h
  have h2 : (2000000 : ℝ) * ((Fast.total7 c7 (cfgOf ω) : ℤ) : ℝ) ≤ 5040 * 4 ^ c7.scale * 801509 := by
    exact_mod_cast h1
  have hs4 : (0 : ℝ) < 5040 * (4 : ℝ) ^ c7.scale := by positivity
  rw [LamF7_sorted c7 hω, div_le_div_iff₀ hs4 (by norm_num)]
  linarith

end BeatAvg
