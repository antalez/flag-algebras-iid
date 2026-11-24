import BeatAvg.Cert.FamSum
import BeatAvg.Five.FlagExpectation

open MeasureTheory Set Function Finset
namespace BeatAvg.Five
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
          f.Q (f.F ((configOf ω).comap (fn l ∘ Fast.appendF f.eR f.eT)) % f.N)
            (f.F ((configOf ω).comap (fn l ∘ Fast.appendF f.eR f.eT')) % f.N)).sum := by
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


end BeatAvg.Five
