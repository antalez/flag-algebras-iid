import BeatAvg.Cert.SqTerm
import BeatAvg.Cert.Transversal
import Fast.Canon

/-!
# The lists of representatives: facts checked by the kernel

For each term of the functional, the list of arrangements used by the checker has no repetition,
has the right length, and consists of injective arrangements that increase on the blocks. With
`sum_perm_reps` this turns sums over all `8!` orderings into sums over the list.
-/

open Function

namespace BeatAvg

theorem fnOf_inj {l l' : List (Fin 8)} (h : l.length = 8) (h' : l'.length = 8)
    (e : Fast.fnOf l = Fast.fnOf l') : l = l' := by
  apply List.ext_getElem (by rw [h, h'])
  intro i h1 h2
  have := congrFun e ⟨i, by omega⟩
  simpa [Fast.fnOf, List.getD, h1, h2] using this

/-- The facts about a list of representatives with three blocks of positions. -/
structure RepFacts (reps : List (List (Fin 8))) {k1 k2 k3 : ℕ} (b1 : Fin k1 → Fin 8)
    (b2 : Fin k2 → Fin 8) (b3 : Fin k3 → Fin 8) (len : ℕ) : Prop where
  nodup : reps.Nodup
  length : reps.length = len
  good : ∀ l ∈ reps, l.length = 8 ∧ Injective (Fast.fnOf l) ∧
    (∀ i j : Fin k1, i < j → Fast.fnOf l (b1 i) < Fast.fnOf l (b1 j)) ∧
    (∀ i j : Fin k2, i < j → Fast.fnOf l (b2 i) < Fast.fnOf l (b2 j)) ∧
    (∀ i j : Fin k3, i < j → Fast.fnOf l (b3 i) < Fast.fnOf l (b3 j))

/-- Sum over all orderings from the facts about the representatives. -/
theorem sum_of_facts {k1 k2 k3 : ℕ} (e1 : Fin k1 ↪ Fin 8) (e2 : Fin k2 ↪ Fin 8)
    (e3 : Fin k3 ↪ Fin 8) (h12 : ∀ i j, e1 i ≠ e2 j) (h13 : ∀ i j, e1 i ≠ e3 j)
    (h23 : ∀ i j, e2 i ≠ e3 j) (F : (Fin 8 → Fin 8) → ℝ)
    (hF1 : ∀ (π : Equiv.Perm (Fin 8)) σ, F ⇑(π * Equiv.Perm.viaEmbedding σ e1) = F ⇑π)
    (hF2 : ∀ (π : Equiv.Perm (Fin 8)) σ, F ⇑(π * Equiv.Perm.viaEmbedding σ e2) = F ⇑π)
    (hF3 : ∀ (π : Equiv.Perm (Fin 8)) σ, F ⇑(π * Equiv.Perm.viaEmbedding σ e3) = F ⇑π)
    {reps : List (List (Fin 8))} {len : ℕ} (hf : RepFacts reps ⇑e1 ⇑e2 ⇑e3 len)
    (hcount : len * (k1.factorial * k2.factorial * k3.factorial) = Nat.factorial 8) :
    ∑ π : Equiv.Perm (Fin 8), F ⇑π
      = ((k1.factorial * k2.factorial * k3.factorial : ℕ) : ℝ)
        * (reps.map fun l => F (Fast.fnOf l)).sum := by
  refine sum_perm_reps e1 e2 e3 h12 h13 h23 F hF1 hF2 hF3 Fast.fnOf reps hf.nodup ?_ ?_ ?_
  · intro l hl l' hl' e
    exact fnOf_inj (hf.good l hl).1 (hf.good l' hl').1 e
  · intro l hl
    obtain ⟨-, hi, g1, g2, g3⟩ := hf.good l hl
    exact ⟨hi, fun i j hij => g1 i j hij, fun i j hij => g2 i j hij, fun i j hij => g3 i j hij⟩
  · rw [hf.length]; exact hcount

/-! ### Blocks of positions -/

def embA : Fin 4 ↪ Fin 8 := ⟨bA, bA_injective⟩
def embB : Fin 4 ↪ Fin 8 := ⟨bB, Fin.natAdd_injective 4 4⟩
def embA3 : Fin 3 ↪ Fin 8 := ⟨fun i => bA i.castSucc, by decide⟩
def embB3 : Fin 3 ↪ Fin 8 := ⟨fun i => bB i.castSucc, by decide⟩
def embR : Fin 2 ↪ Fin 8 := ⟨bR, by decide⟩
def embT : Fin 3 ↪ Fin 8 := ⟨bT, by decide⟩
def embT' : Fin 3 ↪ Fin 8 := ⟨bT', by decide⟩
def embS : Fin 4 ↪ Fin 8 := ⟨bS, by decide⟩
def embW2 : Fin 2 ↪ Fin 8 := ⟨fun i => bW i.castSucc, by decide⟩
def emb0 : Fin 0 ↪ Fin 8 := ⟨fun i => i.elim0, fun i => i.elim0⟩

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem thr_facts : RepFacts Fast.repsThr ⇑embA ⇑embB3 ⇑emb0 280 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem obj_facts : RepFacts Fast.repsObj ⇑embA3 ⇑embB ⇑emb0 280 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem sq_facts : RepFacts Fast.repsSq ⇑embR ⇑embT ⇑embT' 560 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem deg_facts : RepFacts Fast.repsDeg ⇑embS ⇑embW2 ⇑emb0 840 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end BeatAvg
