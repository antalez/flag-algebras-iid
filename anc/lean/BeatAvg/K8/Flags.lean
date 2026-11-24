import BeatAvg.Six.Cover
import BeatAvg.Cert.SortedN
import BeatAvg.K8.Atoms

/-!
# Flags and classes of five points of the sample, read in packed tables

The configuration of five of the eight points, listed in any order, is the configuration of the
pattern of these five points composed with a permutation. For each of the 243 lists of five trits
and each of the permutations that occur, the flag (or class) given by the original definition is
compared with the packed table by evaluation.
-/

open Function

namespace BeatAvg.K8

open BeatAvg

/-! ### Five sorted points -/

def idx5 (a b c d : ℕ) : ℕ := (Fast.combos 5).idxOf (a, b, c, d)

theorem idxOk5 : IdxOk 5 idx5 := by
  intro w x y z d hxy hyz hzd hd
  have h : (Fast.combos 5)[idx5 x y z d]? = some (x, y, z, d) :=
    getElem?_idxOf _ _ (mem_combos.2 ⟨hxy, hyz, hzd, hd⟩)
  simp [patArr, h]

/-- The map `Fin 5 → Fin 8` of a list of five points. -/
def eOf (s : List ℕ) : Fin 5 → Fin 8 := fun i => Fin.ofNat 8 (s.getD i.val 0)

/-- The trits of the five points `e 0 < ... < e 4` of the sample, in the order of `combos 5`. -/
noncomputable def v5 (ω : Fin 8 → ℝ) (e : Fin 5 → Fin 8) : List ℕ :=
  (Fast.combos 5).map (trit (extNn (ω ∘ e)))

theorem sgn_comp {ω : Fin 8 → ℝ} (hω : SG8 ω) {e : Fin 5 → Fin 8} (he : StrictMono e) :
    SGn 5 (ω ∘ e) := by
  refine ⟨hω.mono.comp he, fun i => ?_, fun a b c d had hbd hcd => ?_⟩
  · exact hω.nonneg.trans (hω.mono.monotone (Fin.zero_le _))
  · exact hω.noTie _ _ _ _ (he.injective.ne had) (he.injective.ne hbd) (he.injective.ne hcd)

/-- The configuration of five points of a sorted sample is that of their pattern. -/
theorem cfg_five {ω : Fin 8 → ℝ} (hω : SG8 ω) {e : Fin 5 → Fin 8} (he : StrictMono e) :
    cfgOf (ω ∘ e) = Fast.cfgOfPatG 5 idx5 (v5 ω e).toArray :=
  cfgOf_eq_patG (by norm_num) idxOk5 (sgn_comp hω he)

theorem v5_mem (ω : Fin 8 → ℝ) (e : Fin 5 → Fin 8) : v5 ω e ∈ Six.allTrits 5 := by
  have hlen : (v5 ω e).length = 5 := by rw [v5, List.length_map]; decide
  rw [← hlen]
  apply Six.mem_allTrits
  intro x hx
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
  exact trit_le_two _ q

theorem trit_five (ω : Fin 8 → ℝ) (e : Fin 5 → Fin 8) (a b c d : Fin 5) :
    trit (extNn (ω ∘ e)) (a.val, b.val, c.val, d.val)
      = trit (extN ω) ((e a).val, (e b).val, (e c).val, (e d).val) := by
  simp only [trit, extNn_val, extN_val, comp_apply]

theorem combos5 : Fast.combos 5 = [(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 3, 4), (0, 2, 3, 4), (1, 2, 3, 4)] := by
  decide

/-- Code of a list of five trits. -/
def codeL3 (v : List ℕ) : ℕ :=
  v.getD 0 0 + 3 * (v.getD 1 0 + 3 * (v.getD 2 0 + 3 * (v.getD 3 0 + 3 * v.getD 4 0)))

/-- The five trits, written out. -/
theorem v5_eq (ω : Fin 8 → ℝ) (e : Fin 5 → Fin 8) :
    v5 ω e = [trit (extN ω) ((e 0).val, (e 1).val, (e 2).val, (e 3).val),
      trit (extN ω) ((e 0).val, (e 1).val, (e 2).val, (e 4).val),
      trit (extN ω) ((e 0).val, (e 1).val, (e 3).val, (e 4).val),
      trit (extN ω) ((e 0).val, (e 2).val, (e 3).val, (e 4).val),
      trit (extN ω) ((e 1).val, (e 2).val, (e 3).val, (e 4).val)] := by
  rw [v5, combos5]
  simp only [List.map_cons, List.map_nil]
  rw [← trit_five ω e 0 1 2 3, ← trit_five ω e 0 1 2 4, ← trit_five ω e 0 1 3 4,
    ← trit_five ω e 0 2 3 4, ← trit_five ω e 1 2 3 4]
  rfl

/-! ### Codes of the five-point subsets in the packed pattern -/

theorem trS_two (N k : ℕ) : trS N (2 * k) = tr N k := rfl

theorem mem_ordQ8 {a b c d : ℕ} (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < 8) :
    (a, b, c, d) ∈ ordQ 8 := mem_ordQ.2 ⟨h1, h2, h3, h4⟩

/-- The lists of `subs5` are increasing lists of five points below 8. -/
def incr5 (s : List ℕ) : Bool :=
  s.length == 5 && decide (s.getD 0 0 < s.getD 1 0) && decide (s.getD 1 0 < s.getD 2 0) &&
    decide (s.getD 2 0 < s.getD 3 0) && decide (s.getD 3 0 < s.getD 4 0) && decide (s.getD 4 0 < 8)

theorem subs5_incr : subs5.all incr5 = true := by decide +kernel

theorem subs5_length : subs5.length = 56 := by decide +kernel

theorem eOf_val {s : List ℕ} (hs : incr5 s = true) (i : Fin 5) : (eOf s i).val = s.getD i.val 0 := by
  simp only [incr5, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hs
  have : s.getD i.val 0 < 8 := by
    have hi := i.isLt
    interval_cases hv : i.val <;> omega
  show s.getD i.val 0 % 8 = _
  exact Nat.mod_eq_of_lt this

theorem eOf_mono {s : List ℕ} (hs : incr5 s = true) : StrictMono (eOf s) := by
  have hv := eOf_val hs
  simp only [incr5, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hs
  intro i j hij
  rw [Fin.lt_def, hv, hv]
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val < j.val := hij
  interval_cases hvi : i.val <;> interval_cases hvj : j.val <;> omega

/-- The code of the pattern of the five points `s`, from the packed pattern of the sample. -/
theorem code5_eq {ω : Fin 8 → ℝ} {s : List ℕ} (hs : incr5 s = true) :
    code5 (code 8 (extN ω)) (quads5 s) = codeL3 (v5 ω (eOf s)) := by
  have hv := eOf_val hs
  have hs' := hs
  simp only [incr5, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs'
  obtain ⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hs'
  have key : ∀ q : ℕ × ℕ × ℕ × ℕ, q ∈ ordQ 8 →
      trS (code 8 (extN ω)) (2 * posQ8 q) = trit (extN ω) q := by
    intro q hq
    rw [trS_two, code, tr_packL _ _ (pat_small 8 _), pat_pos _ hq]
  rw [v5_eq, codeL3]
  simp only [List.getD_cons_zero, List.getD_cons_succ, hv, Fin.val_zero, Fin.val_one,
    Fin.val_two]
  have e3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have e4 : ((4 : Fin 5) : ℕ) = 4 := rfl
  simp only [e3, e4, code5, quads5, nadd, nmul]
  rw [key _ (mem_ordQ8 h1 h2 h3 (by omega)), key _ (mem_ordQ8 h1 h2 (by omega) h5),
    key _ (mem_ordQ8 h1 (by omega) h4 h5), key _ (mem_ordQ8 (by omega) h3 h4 h5),
    key _ (mem_ordQ8 h2 h3 h4 h5)]

end BeatAvg.K8

namespace BeatAvg.K8

open BeatAvg

/-! ### The permutations that occur, and the tables -/

/-- Ranks of the positions `0..4` when the roots (positions 0, 1) have the `k`-th pair of ranks. -/
def sigSqL : List (List ℕ) :=
  [[0, 1, 2, 3, 4], [0, 2, 1, 3, 4], [0, 3, 1, 2, 4], [0, 4, 1, 2, 3], [1, 2, 0, 3, 4],
   [1, 3, 0, 2, 4], [1, 4, 0, 2, 3], [2, 3, 0, 1, 4], [2, 4, 0, 1, 3], [3, 4, 0, 1, 2]]

/-- Ranks of the positions `0..4` when the root (position 0) has rank `k`. -/
def sigDegL : List (List ℕ) :=
  [[0, 1, 2, 3, 4], [1, 0, 2, 3, 4], [2, 0, 1, 3, 4], [3, 0, 1, 2, 4], [4, 0, 1, 2, 3]]

def sigOf (L : List (List ℕ)) (k : ℕ) : Fin 5 → Fin 5 :=
  fun i => Fin.ofNat 5 ((L.getD k []).getD i.val 0)

theorem sigSq_inj : ∀ k, k < 10 → Injective (sigOf sigSqL k) := by
  intro k hk
  interval_cases k <;> decide

theorem sigDeg_inj : ∀ k, k < 5 → Injective (sigOf sigDegL k) := by
  intro k hk
  interval_cases k <;> decide

/-- The packed flag table agrees with the original definition of the flag. -/
def flagTabOk (ft : Array ℕ) (ftP : ℕ) : Bool :=
  (Six.allTrits 5).all fun v => (List.range 10).all fun pq =>
    Fast.Fflag ft ((Fast.cfgOfPatG 5 idx5 v.toArray).comap (sigOf sigSqL pq)) % 300
      == Nat.mod (Nat.shiftRight ftP (Nat.add (Nat.mul 90 (codeL3 v)) (9 * pq))) 512

/-- The packed class table agrees with the original definition of the class. -/
def clsTabOk (ct : Array ℕ) (ctP : ℕ) : Bool :=
  (Six.allTrits 5).all fun v => (List.range 5).all fun p =>
    Fast.Fcls ct ((Fast.cfgOfPatG 5 idx5 v.toArray).comap (sigOf sigDegL p))
      == Nat.mod (Nat.shiftRight ctP (Nat.add (Nat.mul 40 (codeL3 v)) (8 * p))) 256

theorem comap_five {ω : Fin 8 → ℝ} (hω : SG8 ω) {s : List ℕ} (hs : incr5 s = true)
    {σ : Fin 5 → Fin 5} (hσ : Injective σ) :
    (cfgOf ω).comap (eOf s ∘ σ) = (Fast.cfgOfPatG 5 idx5 (v5 ω (eOf s)).toArray).comap σ := by
  have he := eOf_mono hs
  rw [← cfgOf_comp ω _ (he.injective.comp hσ), ← cfg_five hω he, ← cfgOf_comp _ σ hσ]
  rfl

theorem flag_of_tab {ft : Array ℕ} {ftP : ℕ} (hT : flagTabOk ft ftP = true) {ω : Fin 8 → ℝ}
    (hω : SG8 ω) {s : List ℕ} (hs : incr5 s = true) {pq : ℕ} (hpq : pq < 10) :
    Fast.Fflag ft ((cfgOf ω).comap (eOf s ∘ sigOf sigSqL pq)) % 300
      = Nat.mod (Nat.shiftRight ftP (Nat.add (Nat.mul 90 (codeL3 (v5 ω (eOf s)))) (9 * pq))) 512 := by
  rw [comap_five hω hs (sigSq_inj pq hpq)]
  simp only [flagTabOk, List.all_eq_true, List.mem_range, beq_iff_eq] at hT
  exact hT _ (v5_mem ω _) pq hpq

theorem cls_of_tab {ct : Array ℕ} {ctP : ℕ} (hT : clsTabOk ct ctP = true) {ω : Fin 8 → ℝ}
    (hω : SG8 ω) {s : List ℕ} (hs : incr5 s = true) {p : ℕ} (hp : p < 5) :
    Fast.Fcls ct ((cfgOf ω).comap (eOf s ∘ sigOf sigDegL p))
      = Nat.mod (Nat.shiftRight ctP (Nat.add (Nat.mul 40 (codeL3 (v5 ω (eOf s)))) (8 * p))) 256 := by
  rw [comap_five hω hs (sigDeg_inj p hp)]
  simp only [clsTabOk, List.all_eq_true, List.mem_range, beq_iff_eq] at hT
  exact hT _ (v5_mem ω _) p hp

/-! ### The packed codes -/

theorem codes_cons (N : ℕ) (ps : ℕ × ℕ × ℕ × ℕ × ℕ) (l : List (ℕ × ℕ × ℕ × ℕ × ℕ)) :
    codes N (ps :: l) = code5 N ps + 256 * codes N l := rfl

theorem codes_digit (N : ℕ) : ∀ (l : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (i : ℕ),
    (∀ ps ∈ l, code5 N ps < 256) → i < l.length →
    Nat.mod (Nat.shiftRight (codes N l) (8 * i)) 256 = code5 N (l.getD i (0, 0, 0, 0, 0))
  | [], i, _, hi => by simp at hi
  | ps :: l, 0, h, _ => by
    have h0 := h ps List.mem_cons_self
    simp only [nmod, nshr, Nat.mul_zero, Nat.shiftRight_zero, List.getD_cons_zero, codes_cons]
    omega
  | ps :: l, i + 1, h, hi => by
    have h0 := h ps List.mem_cons_self
    have ih := codes_digit N l i (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (by simpa using hi)
    simp only [nmod, nshr] at ih ⊢
    rw [List.getD_cons_succ, ← ih, codes_cons, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow]
    have e : 2 ^ (8 * (i + 1)) = 256 * 2 ^ (8 * i) := by rw [Nat.mul_succ, pow_add]; norm_num; ring
    rw [e, ← Nat.div_div_eq_div_mul]
    congr 2
    omega

theorem codeL3_lt (ω : Fin 8 → ℝ) (e : Fin 5 → Fin 8) : codeL3 (v5 ω e) < 256 := by
  rw [v5_eq, codeL3]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  have h := fun q => trit_le_two (extN ω) q
  have h1 := h ((e 0).val, (e 1).val, (e 2).val, (e 3).val)
  have h2 := h ((e 0).val, (e 1).val, (e 2).val, (e 4).val)
  have h3 := h ((e 0).val, (e 1).val, (e 3).val, (e 4).val)
  have h4 := h ((e 0).val, (e 2).val, (e 3).val, (e 4).val)
  have h5 := h ((e 1).val, (e 2).val, (e 3).val, (e 4).val)
  omega

theorem codeL3_le (ω : Fin 8 → ℝ) (e : Fin 5 → Fin 8) : codeL3 (v5 ω e) ≤ 242 := by
  rw [v5_eq, codeL3]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  have h := fun q => trit_le_two (extN ω) q
  have h1 := h ((e 0).val, (e 1).val, (e 2).val, (e 3).val)
  have h2 := h ((e 0).val, (e 1).val, (e 2).val, (e 4).val)
  have h3 := h ((e 0).val, (e 1).val, (e 3).val, (e 4).val)
  have h4 := h ((e 0).val, (e 2).val, (e 3).val, (e 4).val)
  have h5 := h ((e 1).val, (e 2).val, (e 3).val, (e 4).val)
  omega

/-- The code of subset `S`, read in the packed codes. -/
theorem codes_at (ω : Fin 8 → ℝ) {S : ℕ} (hS : S < 56) :
    Nat.mod (Nat.shiftRight (codes (code 8 (extN ω)) sub5Spec) (8 * S)) 256
      = codeL3 (v5 ω (eOf (subs5.getD S []))) := by
  have hall := List.all_eq_true.1 subs5_incr
  have hmem : subs5.getD S [] ∈ subs5 := by
    rw [List.getD_eq_getElem _ _ (by rw [subs5_length]; exact hS)]
    exact List.getElem_mem _
  rw [codes_digit _ _ S ?_ (by rw [sub5Spec, List.length_map, subs5_length]; exact hS)]
  · have : sub5Spec.getD S (0, 0, 0, 0, 0) = quads5 (subs5.getD S []) := by
      rw [sub5Spec, List.getD_eq_getElem _ _ (by rw [List.length_map, subs5_length]; exact hS),
        List.getElem_map, List.getD_eq_getElem _ _ (by rw [subs5_length]; exact hS)]
    rw [this, code5_eq (hall _ hmem)]
  · intro ps hps
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hps
    rw [code5_eq (hall _ hs)]
    exact codeL3_lt ω _

end BeatAvg.K8
