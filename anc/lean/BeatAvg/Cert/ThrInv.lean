import BeatAvg.Cert.ThrTerm

/-!
# The threshold part is invariant under reordering the roots and the three summands
-/

open MeasureTheory Set Function

namespace BeatAvg

/-- Two arrangements agree up to a permutation of the roots (positions `0..3`) and of the first
three fresh points (positions `4..6`). -/
def RelThr (ρ ρ' : Fin 8 → Fin 8) : Prop :=
  (∃ a : Equiv.Perm (Fin 4), ∀ i, ρ (bA i) = ρ' (bA (a i))) ∧ ρ (bB 3) = ρ' (bB 3) ∧
    ∃ b : Equiv.Perm (Fin 3), ∀ i : Fin 3, ρ (bB i.castSucc) = ρ' (bB (b i).castSucc)

instance (ρ ρ' : Fin 8 → Fin 8) : Decidable (RelThr ρ ρ') := by unfold RelThr; infer_instance

theorem S4_congr {f f' : Fin 4 → ℝ} (h3 : f 3 = f' 3) (b : Equiv.Perm (Fin 3))
    (hb : ∀ i : Fin 3, f i.castSucc = f' (b i).castSucc) : f ∈ S4 ↔ f' ∈ S4 := by
  have hs : f 0 + f 1 + f 2 = f' 0 + f' 1 + f' 2 := by
    have h1 : ∑ i : Fin 3, f i.castSucc = ∑ i : Fin 3, f' i.castSucc := by
      rw [← Equiv.sum_comp b (fun i => f' i.castSucc)]
      exact Finset.sum_congr rfl fun i _ => hb i
    simpa [Fin.sum_univ_three] using h1
  simp only [S4, mem_ofPred_eq]
  rw [hs, h3]

theorem forall_lt_congr {f f' : Fin 4 → ℝ} (h3 : f 3 = f' 3) (b : Equiv.Perm (Fin 3))
    (hb : ∀ i : Fin 3, f i.castSucc = f' (b i).castSucc) (t : ℝ) :
    (∀ i, f i < t) ↔ ∀ i, f' i < t := by
  rw [Fin.forall_fin_succ', Fin.forall_fin_succ' (P := fun i => f' i < t)]
  have hl : (Fin.last 3 : Fin 4) = 3 := rfl
  rw [hl, h3]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro h i
    have := h (b.symm i)
    rwa [hb, Equiv.apply_symm_apply] at this
  · intro h i
    rw [hb]; exact h (b i)

theorem thrPart_congr (T : Tab) (ω : Fin 8 → ℝ) {ρ ρ' : Fin 8 → Fin 8} (h : RelThr ρ ρ') (x : ℝ) :
    thrPart T x (ω ∘ ρ) = thrPart T x (ω ∘ ρ') := by
  obtain ⟨⟨a, ha⟩, h3, b, hb⟩ := h
  have hz : sortT ((ω ∘ ρ) ∘ bA) = sortT ((ω ∘ ρ') ∘ bA) := by
    have : (ω ∘ ρ) ∘ bA = ((ω ∘ ρ') ∘ bA) ∘ a := by
      funext i; simp only [comp_apply]; rw [ha]
    rw [this, sortT_comp_perm]
  have hf3 : ((ω ∘ ρ) ∘ bB) 3 = ((ω ∘ ρ') ∘ bB) 3 := by simp only [comp_apply]; rw [h3]
  have hfb : ∀ i : Fin 3, ((ω ∘ ρ) ∘ bB) i.castSucc = ((ω ∘ ρ') ∘ bB) (b i).castSucc := by
    intro i; simp only [comp_apply]; rw [hb]
  have hτ : ∀ θ, T.D.τ θ ((ω ∘ ρ) ∘ bA) = T.D.τ θ ((ω ∘ ρ') ∘ bA) := fun θ => by
    show tau θ (sortT _) = tau θ (sortT _); rw [hz]
  have hu1 : ∀ θ, T.D.u1 θ ((ω ∘ ρ) ∘ bA) = T.D.u1 θ ((ω ∘ ρ') ∘ bA) := fun θ => by
    simp only [Tab.D, mkD]; rw [hz]
  have hu2 : ∀ θ, T.D.u2 θ ((ω ∘ ρ) ∘ bA) = T.D.u2 θ ((ω ∘ ρ') ∘ bA) := fun θ => by
    simp only [Tab.D, mkD]; rw [hz]
  have hS := S4_congr hf3 b hfb
  have hall := fun t => forall_lt_congr hf3 b hfb t
  have hi : ∀ {s : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ))} {p q : (Fin 4 → ℝ) × (Fin 4 → ℝ)},
      (p ∈ s ↔ q ∈ s) → ind s p = ind s q := by
    intro s p q hpq
    by_cases hp : p ∈ s
    · rw [ind_of_mem hp, ind_of_mem (hpq.1 hp)]
    · rw [ind_of_notMem hp, ind_of_notMem (fun hq => hp (hpq.2 hq))]
  have hA1 : ∀ θ, ind (A1 T.D θ) ((ω ∘ ρ) ∘ bA, (ω ∘ ρ) ∘ bB)
      = ind (A1 T.D θ) ((ω ∘ ρ') ∘ bA, (ω ∘ ρ') ∘ bB) := fun θ => by
    apply hi
    show (∀ i, ((ω ∘ ρ) ∘ bB) i < T.D.τ θ ((ω ∘ ρ) ∘ bA)) ↔
      ∀ i, ((ω ∘ ρ') ∘ bB) i < T.D.τ θ ((ω ∘ ρ') ∘ bA)
    rw [hτ]; exact hall _
  have hA2 : ∀ θ, ind (A2 T.D θ) ((ω ∘ ρ) ∘ bA, (ω ∘ ρ) ∘ bB)
      = ind (A2 T.D θ) ((ω ∘ ρ') ∘ bA, (ω ∘ ρ') ∘ bB) := fun θ => by
    apply hi
    show ((ω ∘ ρ) ∘ bB ∈ S4 ∧ ∀ i, ((ω ∘ ρ) ∘ bB) i < T.D.τ θ ((ω ∘ ρ) ∘ bA)) ↔
      ((ω ∘ ρ') ∘ bB ∈ S4 ∧ ∀ i, ((ω ∘ ρ') ∘ bB) i < T.D.τ θ ((ω ∘ ρ') ∘ bA))
    rw [hτ]; exact and_congr hS (hall _)
  have hA3 : ∀ θ, ind (A3 T.D θ) ((ω ∘ ρ) ∘ bA, (ω ∘ ρ) ∘ bB)
      = ind (A3 T.D θ) ((ω ∘ ρ') ∘ bA, (ω ∘ ρ') ∘ bB) := fun θ => by
    apply hi
    show ((ω ∘ ρ) ∘ bB ∈ S4 ∧ ((ω ∘ ρ) ∘ bB) 3 < T.D.τ θ ((ω ∘ ρ) ∘ bA)) ↔
      ((ω ∘ ρ') ∘ bB ∈ S4 ∧ ((ω ∘ ρ') ∘ bB) 3 < T.D.τ θ ((ω ∘ ρ') ∘ bA))
    rw [hτ, hf3]; exact and_congr hS Iff.rfl
  unfold thrPart
  simp only [split_e44, thr1K, thr2K, hA1, hA2, hA3, hu1, hu2]

end BeatAvg
