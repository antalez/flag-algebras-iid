import BeatAvg.K8.FarkasK

/-!
# The levels of the enumeration in nested order

`level_step`: if the level `G` of `k + 1` points contains the pattern of every sample, and
`chkLevel` passes for every pattern of `G`, then the level `G'` of `k + 2` points contains the
pattern of every sample.
-/

namespace BeatAvg.K8

open BeatAvg

theorem mem_lookupG {wb e : ℕ} : ∀ {G : Grouped} {key : ℕ},
    e ∈ unpackE wb (lookupG G key).1 (lookupG G key).2 →
    ∃ g ∈ G, g.1 = key ∧ e ∈ unpackE wb g.2.1 g.2.2
  | [], key, h => by simp [lookupG, unpackE] at h
  | g :: G, key, h => by
    unfold lookupG at h
    cases hb : Nat.beq g.1 key
    · rw [hb, Bool.cond_false] at h
      obtain ⟨g', hg', h1, h2⟩ := mem_lookupG h
      exact ⟨g', List.mem_cons_of_mem _ hg', h1, h2⟩
    · rw [hb, Bool.cond_true] at h
      exact ⟨g, List.mem_cons_self, Nat.eq_of_beq_eq_true hb, h⟩

theorem mem_allCodes {sh wb : ℕ} {G : Grouped} {g : ℕ × ℕ × ℕ} (hg : g ∈ G) {e : ℕ}
    (he : e ∈ unpackE wb g.2.1 g.2.2) : Nat.add g.1 (Nat.shiftLeft e sh) ∈ allCodes sh wb G := by
  induction G with
  | nil => simp at hg
  | cons g' G ih =>
    rw [allCodes, List.mem_append]
    rcases List.mem_cons.1 hg with rfl | hg
    · exact Or.inl (List.mem_map_of_mem he)
    · exact Or.inr (ih hg)

/-- The pattern of a sample of `k + 2` points is among the codes of the level `G`. -/
theorem code_mem_allCodes {G : Grouped} {wb k : ℕ} (hG : LevelOk G wb k) {w : ℕ → ℝ}
    (hw : SG (k + 1) w) :
    code (k + 1) w ∈ allCodes (2 * (ordQ k).length) wb G := by
  obtain ⟨g, hg, hkey, he⟩ := mem_lookupG (hG w hw)
  have e : Nat.add g.1 (Nat.shiftLeft (ext k w) (2 * (ordQ k).length)) = code (k + 1) w := by
    rw [code_succ, hkey, nadd, nshl, Nat.shiftLeft_eq, pow_mul, show (2 : ℕ) ^ 2 = 4 from rfl,
      mul_comm]
  rw [← e]
  exact mem_allCodes hg he

theorem memN_mem : ∀ {l : List ℕ} {x : ℕ}, memN l x = true → x ∈ l
  | [], _, h => by simp [memN] at h
  | a :: l, x, h => by
    unfold memN at h
    cases hb : Nat.beq a x
    · rw [hb, Bool.cond_false] at h; exact List.mem_cons_of_mem _ (memN_mem h)
    · rw [Nat.eq_of_beq_eq_true hb]; exact List.mem_cons_self

theorem extsAll_eq (G : Grouped) (wb k T : ℕ) :
    extsAll G wb (k + 1) T = extsFrom G wb (k + 1) T (candsJ G wb (k + 1) T 0) := rfl

/-- **One level of the enumeration.** -/
theorem level_step {G G' : Grouped} {X : List (ℕ × ℕ × ℕ × ℕ)} {wb wb' k : ℕ}
    (hG : LevelOk G wb k) (hs : statOk k = true)
    (hchk : ∀ U ∈ allCodes (2 * (ordQ k).length) wb G,
      chkLevel G G' X wb wb' (k + 1) (ordQ (k + 2)).length (2 * (ordQ (k + 1)).length) U = true) :
    LevelOk G' wb' (k + 1) := by
  intro w hw
  have hw1 : SG (k + 1) w := ⟨fun i j hij hj => hw.mono i j hij (by omega), hw.nonneg,
    fun a b c d ha hb hc hd => hw.noTie a b c d (by omega) (by omega) (by omega) (by omega)⟩
  have hU := code_mem_allCodes hG hw1
  have hc := hchk _ hU
  have hx := exts_complete hG hs hw
  rw [← extsAll_eq] at hx
  unfold chkLevel at hc
  have hx' := List.all_eq_true.1 hc _ hx
  rw [Bool.or_eq_true] at hx'
  rcases hx' with h | h
  · exact memN_mem h
  · exfalso
    split at h
    · rename_i c _
      have hcode : Nat.add (code (k + 1) w) (Nat.shiftLeft (ext (k + 1) w)
          (2 * (ordQ (k + 1)).length)) = code (k + 2) w := by
        rw [code_succ (k + 1) w, nadd, nshl, Nat.shiftLeft_eq, pow_mul,
          show (2 : ℕ) ^ 2 = 4 from rfl, mul_comm]
      rw [hcode, exclK_false hw] at h
      exact absurd h (by simp)
    · exact absurd h (by simp)

/-- The base: patterns of four points, grouped by the (empty) pattern of three. -/
theorem level_base {G : Grouped} {wb : ℕ} (h3 : ∀ t, t ≤ 2 → t ∈ unpackE wb (lookupG G 0).1 (lookupG G 0).2) :
    LevelOk G wb 3 := by
  intro w _
  have hc : code 3 w = 0 := by
    rw [code, pat, show ordQ 3 = [] from by decide]
    rfl
  have he : ext 3 w = trit w (0, 1, 2, 3) := by
    rw [ext, extL, show triples 3 = [(0, 1, 2)] from by decide]
    simp [packL]
  rw [hc, he]
  exact h3 _ (trit_le_two w _)

end BeatAvg.K8
