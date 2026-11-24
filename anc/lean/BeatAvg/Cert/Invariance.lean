import BeatAvg.Cert.IndexFacts

/-!
# Each part of the functional is invariant under reordering inside its blocks
-/

open Function

namespace BeatAvg

theorem mono_of_lt {k : ℕ} {f : Fin k → Fin 8} (h : ∀ i j, i < j → f i < f j) : Monotone f := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (h i j hlt).le

/-! ### Thresholds: blocks `embA` (roots) and `embB3` (three summands) -/

theorem thr_inv1 (T : Tab) (ω : Fin 8 → ℝ) (x : ℝ) (π : Equiv.Perm (Fin 8))
    (σ : Equiv.Perm (Fin 4)) :
    thrPart T x (ω ∘ ⇑(π * σ.viaEmbedding embA)) = thrPart T x (ω ∘ ⇑π) :=
  thrPart_congr T ω
    ⟨⟨σ, fun i => ext_mem embA π σ i⟩,
      ext_notMem embA π σ (fun i => bB_ne_bA 3 i),
      ⟨1, fun i => ext_notMem embA π σ (fun j => bB_ne_bA _ j)⟩⟩ x

theorem thr_inv2 (T : Tab) (ω : Fin 8 → ℝ) (x : ℝ) (π : Equiv.Perm (Fin 8))
    (σ : Equiv.Perm (Fin 3)) :
    thrPart T x (ω ∘ ⇑(π * σ.viaEmbedding embB3)) = thrPart T x (ω ∘ ⇑π) :=
  thrPart_congr T ω
    ⟨⟨1, fun i => ext_notMem embB3 π σ (fun j => (bB_ne_bA _ i).symm)⟩,
      ext_notMem embB3 π σ (by decide),
      ⟨σ, fun i => ext_mem embB3 π σ i⟩⟩ x

theorem thr_inv3 (T : Tab) (ω : Fin 8 → ℝ) (x : ℝ) (π : Equiv.Perm (Fin 8))
    (σ : Equiv.Perm (Fin 0)) :
    thrPart T x (ω ∘ ⇑(π * σ.viaEmbedding emb0)) = thrPart T x (ω ∘ ⇑π) := by
  rw [ext_empty]

/-! ### Objective: blocks `embA3` (three summands) and `embB` (unused points) -/

theorem obj_inv1 (ω : Fin 8 → ℝ) (π : Equiv.Perm (Fin 8)) (σ : Equiv.Perm (Fin 3)) :
    objT (ω ∘ ⇑(π * σ.viaEmbedding embA3)) = objT (ω ∘ ⇑π) :=
  objT_congr ω ⟨ext_notMem embA3 π σ (by decide), ⟨σ, fun i => ext_mem embA3 π σ i⟩⟩

theorem obj_inv2 (ω : Fin 8 → ℝ) (π : Equiv.Perm (Fin 8)) (σ : Equiv.Perm (Fin 4)) :
    objT (ω ∘ ⇑(π * σ.viaEmbedding embB)) = objT (ω ∘ ⇑π) :=
  objT_congr ω ⟨ext_notMem embB π σ (fun j => (bB_ne_bA j 3).symm),
    ⟨1, fun i => ext_notMem embB π σ (fun j => (bB_ne_bA j _).symm)⟩⟩

theorem obj_inv3 (ω : Fin 8 → ℝ) (π : Equiv.Perm (Fin 8)) (σ : Equiv.Perm (Fin 0)) :
    objT (ω ∘ ⇑(π * σ.viaEmbedding emb0)) = objT (ω ∘ ⇑π) := by
  rw [ext_empty]

/-! ### Squares: blocks `embR`, `embT`, `embT'` -/

theorem sq_inv1 (T : Tab) (ω : Fin 8 → ℝ) (π : Equiv.Perm (Fin 8)) (σ : Equiv.Perm (Fin 2)) :
    sqPart T (ω ∘ ⇑(π * σ.viaEmbedding embR)) = sqPart T (ω ∘ ⇑π) :=
  sqPart_congr T ω
    ⟨⟨σ, fun i => ext_mem embR π σ i⟩,
      ⟨1, fun i => ext_notMem embR π σ (by revert i; decide)⟩,
      ⟨1, fun i => ext_notMem embR π σ (by revert i; decide)⟩⟩

theorem sq_inv2 (T : Tab) (ω : Fin 8 → ℝ) (π : Equiv.Perm (Fin 8)) (σ : Equiv.Perm (Fin 3)) :
    sqPart T (ω ∘ ⇑(π * σ.viaEmbedding embT)) = sqPart T (ω ∘ ⇑π) :=
  sqPart_congr T ω
    ⟨⟨1, fun i => ext_notMem embT π σ (by revert i; decide)⟩,
      ⟨σ, fun i => ext_mem embT π σ i⟩,
      ⟨1, fun i => ext_notMem embT π σ (by revert i; decide)⟩⟩

theorem sq_inv3 (T : Tab) (ω : Fin 8 → ℝ) (π : Equiv.Perm (Fin 8)) (σ : Equiv.Perm (Fin 3)) :
    sqPart T (ω ∘ ⇑(π * σ.viaEmbedding embT')) = sqPart T (ω ∘ ⇑π) :=
  sqPart_congr T ω
    ⟨⟨1, fun i => ext_notMem embT' π σ (by revert i; decide)⟩,
      ⟨1, fun i => ext_notMem embT' π σ (by revert i; decide)⟩,
      ⟨σ, fun i => ext_mem embT' π σ i⟩⟩

/-! ### Degree: blocks `embS` (flag points) and `embW2` (two summands) -/

theorem deg_inv1 (T : Tab) (ω : Fin 8 → ℝ) (x : ℝ) (π : Equiv.Perm (Fin 8))
    (σ : Equiv.Perm (Fin 4)) :
    degPart T x (ω ∘ ⇑(π * σ.viaEmbedding embS)) = degPart T x (ω ∘ ⇑π) :=
  degPart_congr T ω
    ⟨ext_notMem embS π σ (by decide), ⟨σ, fun i => ext_mem embS π σ i⟩,
      ext_notMem embS π σ (by decide),
      ⟨1, fun i => ext_notMem embS π σ (by revert i; decide)⟩⟩ x

theorem deg_inv2 (T : Tab) (ω : Fin 8 → ℝ) (x : ℝ) (π : Equiv.Perm (Fin 8))
    (σ : Equiv.Perm (Fin 2)) :
    degPart T x (ω ∘ ⇑(π * σ.viaEmbedding embW2)) = degPart T x (ω ∘ ⇑π) :=
  degPart_congr T ω
    ⟨ext_notMem embW2 π σ (by decide),
      ⟨1, fun i => ext_notMem embW2 π σ (by revert i; decide)⟩,
      ext_notMem embW2 π σ (by decide), ⟨σ, fun i => ext_mem embW2 π σ i⟩⟩ x

theorem deg_inv3 (T : Tab) (ω : Fin 8 → ℝ) (x : ℝ) (π : Equiv.Perm (Fin 8))
    (σ : Equiv.Perm (Fin 0)) :
    degPart T x (ω ∘ ⇑(π * σ.viaEmbedding emb0)) = degPart T x (ω ∘ ⇑π) := by
  rw [ext_empty]

end BeatAvg
