import BeatAvg.Cert.QPsd
import BeatAvg.Cert.EvalZ

/-!
# The certificate data are valid
-/

open Finset

namespace BeatAvg

theorem evalZ_default : evalZ (default : Fast.Z4) = 0 := by
  show evalZ ⟨0, 0, 0, 0⟩ = 0
  simp [evalZ]

/-- Entry `i` of a table `arr.map (toZ4 Dn)`: zero outside the table, `Dn` times the entry inside. -/
theorem table_entry (arr : Array Fast.K) (Dn : ℤ) (hint : arr.all (Fast.K.integralAt Dn) = true)
    (i : ℕ) : evalZ ((arr.map (Fast.K.toZ4 Dn))[i]!) = Dn * (if h : i < arr.size then evalK arr[i] else 0) := by
  by_cases h : i < arr.size
  · have h' : i < (arr.map (Fast.K.toZ4 Dn)).size := by simpa using h
    rw [getElem!_pos _ i h', dif_pos h, Array.getElem_map]
    exact toZ4_sound (Array.all_eq_true.1 hint i h)
  · have h' : ¬ i < (arr.map (Fast.K.toZ4 Dn)).size := by simpa using h
    rw [getElem!_neg _ i h', dif_neg h, evalZ_default, mul_zero]

theorem table_bounds {c : Fast.Cert8} (he : Encl c.encLo c.encHi c.encM) (arr : Array Fast.K)
    (hint : arr.all (Fast.K.integralAt c.Dn) = true)
    (hb : arr.all (fun x => decide (0 ≤ Fast.K.lowerQ (Fast.encL c) (Fast.encH c) x) &&
      decide (Fast.K.upperQ (Fast.encL c) (Fast.encH c) x ≤ c.B)) = true)
    (hDn : 0 < c.Dn) (hB : 0 ≤ c.B) (i : ℕ) :
    0 ≤ evalZ ((arr.map (Fast.K.toZ4 c.Dn))[i]!) / c.Dn ∧
      evalZ ((arr.map (Fast.K.toZ4 c.Dn))[i]!) / c.Dn ≤ c.B := by
  have hD : (0 : ℝ) < (c.Dn : ℝ) := by exact_mod_cast hDn
  have hB' : (0 : ℝ) ≤ (c.B : ℝ) := by exact_mod_cast hB
  rw [table_entry arr c.Dn hint i, mul_div_cancel_left₀ _ hD.ne']
  by_cases h : i < arr.size
  · rw [dif_pos h]
    have h1 := Array.all_eq_true.1 hb i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    have heQ := enclQ_of he
    have e1 := lowerQ_le heQ arr[i]
    have e2 := le_upperQ heQ arr[i]
    have e3 : (0 : ℝ) ≤ ((Fast.K.lowerQ (Fast.encL c) (Fast.encH c) arr[i] : ℚ) : ℝ) := by
      exact_mod_cast h1.1
    have e4 : ((Fast.K.upperQ (Fast.encL c) (Fast.encH c) arr[i] : ℚ) : ℝ) ≤ (c.B : ℝ) := by
      exact_mod_cast h1.2
    exact ⟨e3.trans e1, e2.trans e4⟩
  · rw [dif_neg h]
    exact ⟨le_refl _, hB'⟩

end BeatAvg

namespace BeatAvg

open Finset

theorem ofFn_getElem! {n : ℕ} (f : Fin n → Fast.Z4) (k : ℕ) (hk : k < n) :
    (Array.ofFn f)[k]! = f ⟨k, hk⟩ := by
  have hs : k < (Array.ofFn f).size := by simpa using hk
  rw [getElem!_pos (Array.ofFn f) k hs, Array.getElem_ofFn]

theorem flatMap_map_nil {α β γ : Type*} (l : List α) (f : α → γ → β) :
    (l.flatMap fun e => ([] : List γ).map (f e)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [List.flatMap_cons] using ih

theorem QKw_nil (Yr : List (List Fast.K)) (wi : List (ℕ × Fast.K)) (n : ℤ) :
    (Fast.QKw Yr wi []).integralAt n = true := by
  unfold Fast.QKw
  rw [flatMap_map_nil]
  simp [Fast.ksum, Fast.K.integralAt, Fast.K.zero]

theorem QZ_entry (c : Fast.Cert8) (hint : Fast.integralOk c = true) (hDn : 0 < c.Dn) {i j : ℕ}
    (hi : i < 300) (hj : j < 300) :
    evalZ ((Fast.tabsOf c).QZ[i * 300 + j]!) / c.Dn = evalK (Fast.QK c i j) := by
  have hD : (0 : ℝ) < (c.Dn : ℝ) := by exact_mod_cast hDn
  have hk : i * 300 + j < 90000 := by omega
  have hQZ : (Fast.tabsOf c).QZ = Array.ofFn (Fast.qzFn c) := by
    simp only [Fast.tabsOf]
  have h1 : (Fast.tabsOf c).QZ[i * 300 + j]!
      = (Fast.QK c ((i * 300 + j) / 300) ((i * 300 + j) % 300)).toZ4 c.Dn := by
    rw [hQZ, ofFn_getElem! (Fast.qzFn c) _ hk]
    simp only [Fast.qzFn, Fast.qzAt]
  have e1 : (i * 300 + j) / 300 = i := by omega
  have e2 : (i * 300 + j) % 300 = j := by omega
  rw [h1, e1, e2]
  have h2 : (Fast.QK c i j).integralAt c.Dn = true := by
    simp only [Fast.integralOk, Bool.and_eq_true] at hint
    have hrow := List.all_eq_true.1 hint.1.1.1.1 i (List.mem_range.2 hi)
    unfold Fast.intRow at hrow
    unfold Fast.QK
    by_cases hjs : j < c.W.size
    · refine List.all_eq_true.1 hrow _ ?_
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjs]
      simp
    · rw [show c.W.getD j [] = [] by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl]
      exact QKw_nil _ _ _
  rw [toZ4_sound h2, mul_div_cancel_left₀ _ hD.ne']

/-- The certificate data are valid. -/
theorem cert_valid (c : Fast.Cert8) (h : Fast.staticOk c = true) :
    (tabOf (Fast.tabsOf c)).D.Valid (c.B : ℝ) := by
  simp only [Fast.staticOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨henc, hint⟩, hpsd⟩, hW⟩, hmult⟩, hDn⟩, -⟩, hB⟩ := h
  have he := enclosure_sound henc
  have hint' := hint
  simp only [Fast.integralOk, Bool.and_eq_true] at hint'
  obtain ⟨⟨⟨⟨-, hilo⟩, hihi⟩, hiw1⟩, hiw2⟩ := hint'
  simp only [Fast.multOk, Bool.and_eq_true] at hmult
  obtain ⟨⟨⟨hmlo, hmhi⟩, hmw1⟩, hmw2⟩ := hmult
  refine mkD_valid _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · intro v
    have hQ := Q_psd c he hpsd hW v
    have e : ∀ i j : Fin 300, (tabOf (Fast.tabsOf c)).Qf i.val j.val = evalK (Fast.QK c i.val j.val) :=
      fun i j => QZ_entry c hint hDn i.isLt j.isLt
    simp only [e]
    exact hQ
  · intro k; exact table_bounds he c.lo (by rw [← Array.all_toList]; exact hilo)
      (by rw [← Array.all_toList]; exact hmlo) hDn hB k
  · intro k; exact table_bounds he c.hi (by rw [← Array.all_toList]; exact hihi)
      (by rw [← Array.all_toList]; exact hmhi) hDn hB k
  · intro k; exact table_bounds he c.w1 (by rw [← Array.all_toList]; exact hiw1)
      (by rw [← Array.all_toList]; exact hmw1) hDn hB k
  · intro k; exact table_bounds he c.w2 (by rw [← Array.all_toList]; exact hiw2)
      (by rw [← Array.all_toList]; exact hmw2) hDn hB k

end BeatAvg
