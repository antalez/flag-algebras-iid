import BeatAvg.Cert.SortedN
import BeatAvg.Cert.FamSum
import Fast.Canon7

/-!
# The lists of arrangements of seven points: facts checked by the kernel
-/

open Function

namespace BeatAvg

theorem fnOf7_inj {l l' : List (Fin 7)} (h : l.length = 7) (h' : l'.length = 7)
    (e : Fast.fnOf7 l = Fast.fnOf7 l') : l = l' := by
  apply List.ext_getElem (by rw [h, h'])
  intro i h1 h2
  have := congrFun e ⟨i, by omega⟩
  simpa [Fast.fnOf7, List.getD, h1, h2] using this

/-- The facts needed for one block structure: the list `reps` has no repetition, `7!/k` members
with `k = t! m! m!`, and its members are injective and increase on the three blocks. -/
structure FamFacts (t m : ℕ) (reps : List (List (Fin 7))) (k : ℕ) : Prop where
  nodup : reps.Nodup
  count : reps.length * k = 5040
  kfac : k = t.factorial * m.factorial * m.factorial
  good : ∀ l ∈ reps, l.length = 7 ∧ Injective (Fast.fnOf7 l) ∧
    Injective (Fast.fnOf7 l ∘ Fast.appendF (Fast.eR7 t) (Fast.eT7 t m)) ∧
    Injective (Fast.fnOf7 l ∘ Fast.appendF (Fast.eR7 t) (Fast.eT7' t m)) ∧
    (∀ i j : Fin t, i < j → Fast.fnOf7 l (Fast.eR7 t i) < Fast.fnOf7 l (Fast.eR7 t j)) ∧
    (∀ i j : Fin m, i < j → Fast.fnOf7 l (Fast.eT7 t m i) < Fast.fnOf7 l (Fast.eT7 t m j)) ∧
    (∀ i j : Fin m, i < j → Fast.fnOf7 l (Fast.eT7' t m i) < Fast.fnOf7 l (Fast.eT7' t m j))
  inj : Injective (Sum.elim (Fast.eR7 t) (Sum.elim (Fast.eT7 t m) (Fast.eT7' t m)))

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem facts14 : FamFacts 1 3 Fast.reps14 36 :=
  ⟨by decide +kernel, by decide +kernel, by decide, by decide +kernel, by decide⟩

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem facts24 : FamFacts 2 2 Fast.reps24 8 :=
  ⟨by decide +kernel, by decide +kernel, by decide, by decide +kernel, by decide⟩

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem facts35 : FamFacts 3 2 Fast.reps35 24 :=
  ⟨by decide +kernel, by decide +kernel, by decide, by decide +kernel, by decide⟩

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem facts45 : FamFacts 4 1 Fast.reps45 24 :=
  ⟨by decide +kernel, by decide +kernel, by decide, by decide +kernel, by decide⟩

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem facts56 : FamFacts 5 1 Fast.reps56 120 :=
  ⟨by decide +kernel, by decide +kernel, by decide, by decide +kernel, by decide⟩

theorem e47_inj : Injective Fast.e47 := by decide

/-- The two blocks of the objective term: the three summands and the three unused points. -/
def embO1 : Fin 3 ↪ Fin 7 := ⟨fun i => Fast.e47 i.castSucc, by decide⟩
def embO2 : Fin 3 ↪ Fin 7 := ⟨fun i => Fin.ofNat 7 (4 + i.val), by decide⟩

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem obj7_nodup : Fast.repsObj7.Nodup := by decide +kernel

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem obj7_length : Fast.repsObj7.length = 140 := by decide +kernel

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem obj7_good : ∀ l ∈ Fast.repsObj7, l.length = 7 ∧ Injective (Fast.fnOf7 l) ∧
    (∀ i j : Fin 3, i < j → Fast.fnOf7 l (embO1 i) < Fast.fnOf7 l (embO1 j)) ∧
    (∀ i j : Fin 3, i < j → Fast.fnOf7 l (embO2 i) < Fast.fnOf7 l (embO2 j)) := by
  decide +kernel

end BeatAvg
