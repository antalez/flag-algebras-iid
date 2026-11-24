import BeatAvg.Bounded
import BeatAvg.Degree

/-!
# The eight-point functional

For certificate data `D` (a flag map with a quadratic form, degree weights, thresholds with weights,
a constant `c_lo`), `lam D x ω` is the non-symmetrised functional of a sample `ω : Fin 8 → ℝ` and
`Lam D x ω` its average over all permutations of the eight points. `Lam D x ω` is the sample form of
`Λ_P(x)` in `theorem_D_proof.md`, section 7.
-/

open MeasureTheory Set Function

namespace BeatAvg

/-! ### Index maps -/

/-- Four roots, four fresh points. -/
def e44 : Fin 4 ⊕ Fin 4 → Fin 8 := finSumFinEquiv

/-- Two roots and two triples. -/
def e233 : Fin 2 ⊕ (Fin 3 ⊕ Fin 3) → Fin 8 := fun s => finSumFinEquiv (Sum.map id finSumFinEquiv s)

/-- One root, four flag points, three further points. -/
def e143 : Fin 1 ⊕ (Fin 4 ⊕ Fin 3) → Fin 8 := fun s => finSumFinEquiv (Sum.map id finSumFinEquiv s)

theorem e44_injective : Injective e44 := finSumFinEquiv.injective

theorem e233_injective : Injective e233 :=
  finSumFinEquiv.injective.comp (Sum.map_injective.2 ⟨injective_id, finSumFinEquiv.injective⟩)

theorem e143_injective : Injective e143 :=
  finSumFinEquiv.injective.comp (Sum.map_injective.2 ⟨injective_id, finSumFinEquiv.injective⟩)

/-! ### Certificate data -/

/-- The data of a certificate, in sample form. -/
structure CertData (nΦ : ℕ) (Θ : Type) where
  /-- the flag of two roots and three further points -/
  flag : (Fin 2 → ℝ) × (Fin 3 → ℝ) → Fin nΦ
  /-- the quadratic form on flags -/
  Q : Fin nΦ → Fin nΦ → ℝ
  /-- lower degree weight, a function of a root and four flag points -/
  alo : ℝ × (Fin 4 → ℝ) → ℝ
  /-- upper degree weight -/
  ahi : ℝ × (Fin 4 → ℝ) → ℝ
  /-- thresholds, functions of four roots -/
  τ : Θ → (Fin 4 → ℝ) → ℝ
  /-- weights of the sub-law constraints, functions of four roots -/
  u1 : Θ → (Fin 4 → ℝ) → ℝ
  /-- weights of the substitution constraints -/
  u2 : Θ → (Fin 4 → ℝ) → ℝ
  /-- the lower constant -/
  clo : ℝ

/-- Validity of certificate data: measurability, positive semidefiniteness of the quadratic form,
and weights with values in `[0, B]`. -/
structure CertData.Valid {nΦ : ℕ} {Θ : Type} (D : CertData nΦ Θ) (B : ℝ) : Prop where
  flag_meas : Measurable D.flag
  Q_psd : ∀ v : Fin nΦ → ℝ, 0 ≤ ∑ i, ∑ j, v i * D.Q i j * v j
  alo_meas : Measurable D.alo
  ahi_meas : Measurable D.ahi
  τ_meas : ∀ θ, Measurable (D.τ θ)
  u1_meas : ∀ θ, Measurable (D.u1 θ)
  u2_meas : ∀ θ, Measurable (D.u2 θ)
  alo_nonneg : ∀ p, 0 ≤ D.alo p
  alo_le : ∀ p, D.alo p ≤ B
  ahi_nonneg : ∀ p, 0 ≤ D.ahi p
  ahi_le : ∀ p, D.ahi p ≤ B
  u1_nonneg : ∀ θ ρ, 0 ≤ D.u1 θ ρ
  u1_le : ∀ θ ρ, D.u1 θ ρ ≤ B
  u2_nonneg : ∀ θ ρ, 0 ≤ D.u2 θ ρ
  u2_le : ∀ θ ρ, D.u2 θ ρ ≤ B

variable {nΦ : ℕ} {Θ : Type}

/-! ### The terms -/

/-- Objective term: the first four points succeed. -/
noncomputable def objT (ω : Fin 8 → ℝ) : ℝ := ind S4 (split e44 ω).1

/-- Square term, as a function of (roots, triple, triple). -/
noncomputable def sqK (D : CertData nΦ Θ) (p : (Fin 2 → ℝ) × ((Fin 3 → ℝ) × (Fin 3 → ℝ))) : ℝ :=
  D.Q (D.flag (p.1, p.2.1)) (D.flag (p.1, p.2.2))

/-- Number of successful positions when `x` is inserted among the three points `w`. -/
noncomputable def s4 (x : ℝ) (w : Fin 3 → ℝ) : ℝ := ∑ i : Fin 4, ind S4 (Fin.insertNth i x w)

/-- Lower degree term, as a function of (root, flag points, three points). -/
noncomputable def degLoK (D : CertData nΦ Θ)
    (p : (Fin 1 → ℝ) × ((Fin 4 → ℝ) × (Fin 3 → ℝ))) : ℝ :=
  D.alo (p.1 0, p.2.1) * (s4 (p.1 0) p.2.2 / 4 - D.clo)

/-- Upper degree term. -/
noncomputable def degHiK (D : CertData nΦ Θ) (x : ℝ)
    (p : (Fin 1 → ℝ) × ((Fin 4 → ℝ) × (Fin 3 → ℝ))) : ℝ :=
  D.ahi (p.1 0, p.2.1) * (x - s4 (p.1 0) p.2.2 / 4)

/-- All fresh points below the threshold. -/
def A1 (D : CertData nΦ Θ) (θ : Θ) : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ)) :=
  {p | ∀ i, p.2 i < D.τ θ p.1}

/-- The fresh points succeed and all lie below the threshold. -/
def A2 (D : CertData nΦ Θ) (θ : Θ) : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ)) :=
  {p | p.2 ∈ S4 ∧ ∀ i, p.2 i < D.τ θ p.1}

/-- The fresh points succeed and the target lies below the threshold. -/
def A3 (D : CertData nΦ Θ) (θ : Θ) : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ)) :=
  {p | p.2 ∈ S4 ∧ p.2 3 < D.τ θ p.1}

/-- Sub-law term, as a function of (roots, fresh points). -/
noncomputable def thr1K (D : CertData nΦ Θ) (θ : Θ) (x : ℝ)
    (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) : ℝ :=
  D.u1 θ p.1 * (x * ind (A1 D θ) p - ind (A2 D θ) p)

/-- Substitution term. -/
noncomputable def thr2K (D : CertData nΦ Θ) (θ : Θ) (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) : ℝ :=
  D.u2 θ p.1 * (ind (A3 D θ) p - D.clo * ind (A1 D θ) p)

/-- The non-symmetrised functional. -/
noncomputable def lam [Fintype Θ] (D : CertData nΦ Θ) (x : ℝ) (ω : Fin 8 → ℝ) : ℝ :=
  objT ω + sqK D (split3 e233 ω) + degLoK D (split3 e143 ω) + degHiK D x (split3 e143 ω)
    + ∑ θ, (thr1K D θ x (split e44 ω) + thr2K D θ (split e44 ω))

/-- The functional `Λ(x)` of a sample: the average of `lam` over all orderings of the points. -/
noncomputable def Lam [Fintype Θ] (D : CertData nΦ Θ) (x : ℝ) (ω : Fin 8 → ℝ) : ℝ :=
  (1 / (Nat.factorial 8 : ℝ)) * ∑ π : Equiv.Perm (Fin 8), lam D x (ω ∘ π)

/-! ### Affine dependence on `x` -/

/-- Slope of `lam` in `x`. -/
noncomputable def lamV [Fintype Θ] (D : CertData nΦ Θ) (ω : Fin 8 → ℝ) : ℝ :=
  D.ahi ((split3 e143 ω).1 0, (split3 e143 ω).2.1)
    + ∑ θ, D.u1 θ (split e44 ω).1 * ind (A1 D θ) (split e44 ω)

theorem lam_affine [Fintype Θ] (D : CertData nΦ Θ) (x : ℝ) (ω : Fin 8 → ℝ) :
    lam D x ω = lam D 0 ω + x * lamV D ω := by
  simp only [lam, lamV, degHiK, thr1K, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  have : ∀ θ, D.u1 θ (split e44 ω).1 * (x * ind (A1 D θ) (split e44 ω) - ind (A2 D θ) (split e44 ω))
      = D.u1 θ (split e44 ω).1 * (0 * ind (A1 D θ) (split e44 ω) - ind (A2 D θ) (split e44 ω))
        + x * (D.u1 θ (split e44 ω).1 * ind (A1 D θ) (split e44 ω)) := fun θ => by ring
  simp only [this, Finset.sum_add_distrib]
  ring

theorem Lam_affine [Fintype Θ] (D : CertData nΦ Θ) (x : ℝ) (ω : Fin 8 → ℝ) :
    Lam D x ω = Lam D 0 ω
      + x * ((1 / (Nat.factorial 8 : ℝ)) * ∑ π : Equiv.Perm (Fin 8), lamV D (ω ∘ π)) := by
  simp only [Lam]
  have : ∀ π : Equiv.Perm (Fin 8), lam D x (ω ∘ π) = lam D 0 (ω ∘ π) + x * lamV D (ω ∘ π) :=
    fun π => lam_affine D x _
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- `Λ` at a convex combination. -/
theorem Lam_convex [Fintype Θ] (D : CertData nΦ Θ) (x y s : ℝ) (ω : Fin 8 → ℝ) :
    Lam D ((1 - s) * x + s * y) ω = (1 - s) * Lam D x ω + s * Lam D y ω := by
  rw [Lam_affine D ((1 - s) * x + s * y), Lam_affine D x, Lam_affine D y]
  ring

end BeatAvg
