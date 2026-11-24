import BeatAvg.Cert.FlagBound
import BeatAvg.Cert.Transversal
import BeatAvg.Cert.ThrInv
import BeatAvg.Cert.PatSbG

/-!
# Sums over all orderings for a square family and for the objective; sorted samples on `n` points
-/

open MeasureTheory Set Function Finset

namespace BeatAvg

variable {n t m : ℕ}

/-- Sum of a square term over all orderings of a sorted sample, as a sum over a list of
arrangements that increase on the three blocks. -/
theorem Fam.sum_perm (f : Fam n t m) (hinj : Injective (Sum.elim f.eR (Sum.elim f.eT f.eT')))
    (fn : List (Fin n) → Fin n → Fin n) (reps : List (List (Fin n))) (hnodup : reps.Nodup)
    (hfn : ∀ l ∈ reps, ∀ l' ∈ reps, fn l = fn l' → l = l')
    (hgood : ∀ l ∈ reps, Injective (fn l) ∧ Injective (fn l ∘ Fast.appendF f.eR f.eT) ∧
      Injective (fn l ∘ Fast.appendF f.eR f.eT') ∧ StrictMono (fn l ∘ f.eR) ∧
      StrictMono (fn l ∘ f.eT) ∧ StrictMono (fn l ∘ f.eT'))
    (hcount : reps.length * (t.factorial * m.factorial * m.factorial) = n.factorial)
    {ω : Fin n → ℝ} (hω : Monotone ω) :
    ∑ π : Equiv.Perm (Fin n), f.term (ω ∘ ⇑π)
      = ((t.factorial * m.factorial * m.factorial : ℕ) : ℝ) * (reps.map fun l =>
          f.Q (f.F ((cfgOf ω).comap (fn l ∘ Fast.appendF f.eR f.eT)) % f.N)
            (f.F ((cfgOf ω).comap (fn l ∘ Fast.appendF f.eR f.eT')) % f.N)).sum := by
  have iR : Injective f.eR := fun a b h =>
    Sum.inl_injective (hinj (a₁ := Sum.inl a) (a₂ := Sum.inl b) h)
  have iT : Injective f.eT := fun a b h =>
    Sum.inl_injective (Sum.inr_injective
      (hinj (a₁ := Sum.inr (Sum.inl a)) (a₂ := Sum.inr (Sum.inl b)) h))
  have iT' : Injective f.eT' := fun a b h =>
    Sum.inr_injective (Sum.inr_injective
      (hinj (a₁ := Sum.inr (Sum.inr a)) (a₂ := Sum.inr (Sum.inr b)) h))
  have dRT : ∀ i j, f.eR i ≠ f.eT j := fun i j h =>
    Sum.inl_ne_inr (hinj (a₁ := Sum.inl i) (a₂ := Sum.inr (Sum.inl j)) h)
  have dRT' : ∀ i j, f.eR i ≠ f.eT' j := fun i j h =>
    Sum.inl_ne_inr (hinj (a₁ := Sum.inl i) (a₂ := Sum.inr (Sum.inr j)) h)
  have dTT' : ∀ i j, f.eT i ≠ f.eT' j := fun i j h =>
    Sum.inl_ne_inr (Sum.inr_injective
      (hinj (a₁ := Sum.inr (Sum.inl i)) (a₂ := Sum.inr (Sum.inr j)) h))
  obtain ⟨e1, he1⟩ : ∃ e : Fin t ↪ Fin n, ⇑e = f.eR := ⟨⟨f.eR, iR⟩, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e : Fin m ↪ Fin n, ⇑e = f.eT := ⟨⟨f.eT, iT⟩, rfl⟩
  obtain ⟨e3, he3⟩ : ∃ e : Fin m ↪ Fin n, ⇑e = f.eT' := ⟨⟨f.eT', iT'⟩, rfl⟩
  have h := sum_perm_reps e1 e2 e3 (by rw [he1, he2]; exact dRT) (by rw [he1, he3]; exact dRT')
    (by rw [he2, he3]; exact dTT') (fun ρ => f.term (ω ∘ ρ))
    (fun π σ => f.term_congr ω
      ⟨⟨σ, fun i => by rw [← he1]; exact ext_mem e1 π σ i⟩,
        ⟨1, fun i => ext_notMem e1 π σ (by rw [he1]; exact fun j => (dRT j i).symm)⟩,
        ⟨1, fun i => ext_notMem e1 π σ (by rw [he1]; exact fun j => (dRT' j i).symm)⟩⟩)
    (fun π σ => f.term_congr ω
      ⟨⟨1, fun i => ext_notMem e2 π σ (by rw [he2]; exact fun j => dRT i j)⟩,
        ⟨σ, fun i => by rw [← he2]; exact ext_mem e2 π σ i⟩,
        ⟨1, fun i => ext_notMem e2 π σ (by rw [he2]; exact fun j => (dTT' j i).symm)⟩⟩)
    (fun π σ => f.term_congr ω
      ⟨⟨1, fun i => ext_notMem e3 π σ (by rw [he3]; exact fun j => dRT' i j)⟩,
        ⟨1, fun i => ext_notMem e3 π σ (by rw [he3]; exact fun j => dTT' i j)⟩,
        ⟨σ, fun i => by rw [← he3]; exact ext_mem e3 π σ i⟩⟩)
    fn reps hnodup hfn
    (fun l hl => by
      obtain ⟨h0, -, -, h3, h4, h5⟩ := hgood l hl
      rw [he1, he2, he3]
      exact ⟨h0, h3, h4, h5⟩)
    hcount
  rw [h]
  congr 2
  refine List.map_congr_left fun l hl => ?_
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := hgood l hl
  exact f.term_eval hω h1 h2 h3.monotone h4.monotone h5.monotone

/-- Same target, summands up to a permutation. -/
def RelObjG (e4 : Fin 4 → Fin n) (ρ ρ' : Fin n → Fin n) : Prop :=
  ρ (e4 3) = ρ' (e4 3) ∧
    ∃ b : Equiv.Perm (Fin 3), ∀ i : Fin 3, ρ (e4 i.castSucc) = ρ' (e4 (b i).castSucc)

instance (e4 : Fin 4 → Fin n) (ρ ρ' : Fin n → Fin n) : Decidable (RelObjG e4 ρ ρ') := by
  unfold RelObjG; infer_instance

theorem objG_congr (e4 : Fin 4 → Fin n) (ω : Fin n → ℝ) {ρ ρ' : Fin n → Fin n}
    (h : RelObjG e4 ρ ρ') : objG e4 (ω ∘ ρ) = objG e4 (ω ∘ ρ') := by
  obtain ⟨h3, b, hb⟩ := h
  unfold objG
  have hS : (ω ∘ ρ) ∘ e4 ∈ S4 ↔ (ω ∘ ρ') ∘ e4 ∈ S4 :=
    S4_congr (by simp only [comp_apply]; rw [h3]) b (fun i => by simp only [comp_apply]; rw [hb])
  by_cases hp : (ω ∘ ρ) ∘ e4 ∈ S4
  · rw [ind_of_mem hp, ind_of_mem (hS.1 hp)]
  · rw [ind_of_notMem hp, ind_of_notMem (fun hq => hp (hS.2 hq))]

theorem objG_eval (e4 : Fin 4 → Fin n) (ω : Fin n → ℝ) {ρ : Fin n → Fin n}
    (hinj : Injective (ρ ∘ e4)) :
    objG e4 (ω ∘ ρ)
      = if (cfgOf ω).sb (ρ (e4 0)) (ρ (e4 1)) (ρ (e4 2)) (ρ (e4 3)) then 1 else 0 := by
  have hne : ∀ {i j : Fin 4}, i ≠ j → ρ (e4 i) ≠ ρ (e4 j) := fun h => hinj.ne h
  unfold objG
  apply ind_eq_ite_bool
  rw [sb_cfgOf ω (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide))]
  rfl

/-- Sum of the objective term over all orderings: the summands `b1` and the unused points `b2`
are the two blocks. -/
theorem objG_sum_perm (e4 : Fin 4 → Fin n) (he4 : Injective e4) (b1 : Fin 3 ↪ Fin n)
    (hb1 : ∀ i, b1 i = e4 i.castSucc) {k2 : ℕ} (b2 : Fin k2 ↪ Fin n)
    (h2 : ∀ i j, e4 i ≠ b2 j)
    (fn : List (Fin n) → Fin n → Fin n) (reps : List (List (Fin n))) (hnodup : reps.Nodup)
    (hfn : ∀ l ∈ reps, ∀ l' ∈ reps, fn l = fn l' → l = l')
    (hgood : ∀ l ∈ reps, Injective (fn l) ∧ StrictMono (fn l ∘ ⇑b1) ∧ StrictMono (fn l ∘ ⇑b2))
    (hcount : reps.length * (Nat.factorial 3 * k2.factorial * Nat.factorial 0) = n.factorial)
    (ω : Fin n → ℝ) :
    ∑ π : Equiv.Perm (Fin n), objG e4 (ω ∘ ⇑π)
      = ((Nat.factorial 3 * k2.factorial * Nat.factorial 0 : ℕ) : ℝ) * (reps.map fun l =>
          if (cfgOf ω).sb (fn l (e4 0)) (fn l (e4 1)) (fn l (e4 2)) (fn l (e4 3)) then (1 : ℝ)
          else 0).sum := by
  have h3 : ∀ i, e4 3 ≠ b1 i := fun i h => by
    rw [hb1] at h
    have hne : ∀ i : Fin 3, (3 : Fin 4) ≠ i.castSucc := by decide
    exact hne i (he4 h)
  have h := sum_perm_reps b1 b2 (emb0n n) (fun i j => by rw [hb1]; exact h2 _ j)
    (fun _ j => j.elim0) (fun _ j => j.elim0) (fun ρ => objG e4 (ω ∘ ρ))
    (fun π σ => objG_congr e4 ω
      ⟨ext_notMem b1 π σ h3, ⟨σ, fun i => by rw [← hb1, ← hb1]; exact ext_mem b1 π σ i⟩⟩)
    (fun π σ => objG_congr e4 ω
      ⟨ext_notMem b2 π σ (h2 3), ⟨1, fun i => ext_notMem b2 π σ (h2 _)⟩⟩)
    (fun π σ => by rw [ext_empty])
    fn reps hnodup hfn
    (fun l hl => by
      obtain ⟨h0, g1, g2⟩ := hgood l hl
      exact ⟨h0, g1, g2, fun i => i.elim0⟩)
    hcount
  rw [h]
  congr 2
  exact List.map_congr_left fun l hl => objG_eval e4 ω ((hgood l hl).1.comp he4)

end BeatAvg
