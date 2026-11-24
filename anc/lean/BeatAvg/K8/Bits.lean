import Mathlib.Tactic
import BeatAvg.K8.Search

/-!
# Packed lists of trits: arithmetic and bitwise lemmas
-/

namespace BeatAvg.K8

theorem nadd (a b : ℕ) : Nat.add a b = a + b := rfl
theorem nmul (a b : ℕ) : Nat.mul a b = a * b := rfl
theorem ndiv (a b : ℕ) : Nat.div a b = a / b := rfl
theorem nmod (a b : ℕ) : Nat.mod a b = a % b := rfl
theorem nland (a b : ℕ) : Nat.land a b = a &&& b := rfl
theorem nlor (a b : ℕ) : Nat.lor a b = a ||| b := rfl
theorem nxor (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
theorem nshr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
theorem nshl (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl
theorem npow (a b : ℕ) : Nat.pow a b = a ^ b := rfl

/-- All entries are trits in the wide sense (two bits). -/
def Small (xs : List ℕ) : Prop := ∀ x ∈ xs, x < 4

theorem Small.tail {x : ℕ} {xs : List ℕ} (h : Small (x :: xs)) : Small xs :=
  fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem Small.head {x : ℕ} {xs : List ℕ} (h : Small (x :: xs)) : x < 4 := h x List.mem_cons_self

theorem packL_cons (x : ℕ) (xs : List ℕ) : packL (x :: xs) = x + 4 * packL xs := rfl

theorem packL_lt : ∀ {xs : List ℕ}, Small xs → packL xs < 4 ^ xs.length
  | [], _ => by simp [packL]
  | x :: xs, h => by
    have h1 := h.head
    have h2 := packL_lt h.tail
    rw [packL_cons, List.length_cons, pow_succ]
    omega

theorem packL_append : ∀ (a b : List ℕ), packL (a ++ b) = packL a + 4 ^ a.length * packL b
  | [], b => by simp [packL]
  | x :: a, b => by
    rw [List.cons_append, packL_cons, packL_cons, packL_append a b, List.length_cons, pow_succ]
    ring

/-- Keep the entries whose flag is `true`. -/
def pick : List Bool → List ℕ → List ℕ
  | true :: bs, x :: xs => x :: pick bs xs
  | false :: bs, _ :: xs => pick bs xs
  | _, _ => []

/-- Replace by zero the entries whose flag is `false`. -/
def zeroOut : List Bool → List ℕ → List ℕ
  | true :: bs, x :: xs => x :: zeroOut bs xs
  | false :: bs, _ :: xs => 0 :: zeroOut bs xs
  | _, _ => []

theorem pick_map {α : Type} (p : α → Bool) (f : α → ℕ) :
    ∀ l : List α, pick (l.map p) (l.map f) = (l.filter p).map f
  | [] => rfl
  | a :: l => by
    cases h : p a <;> simp [pick, h, pick_map p f l]

theorem gatherM_packL : ∀ (bs : List Bool) (xs : List ℕ), Small xs → bs.length = xs.length →
    gatherM bs (packL xs) = packL (pick bs xs)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | b :: bs, x :: xs, hs, hl => by
    have hx := hs.head
    have ih := gatherM_packL bs xs hs.tail (by simpa using hl)
    have e1 : (x + 4 * packL xs) / 4 = packL xs := by omega
    have e2 : (x + 4 * packL xs) % 4 = x := by omega
    cases b
    · simp only [gatherM, pick, packL_cons, ndiv, e1, ih]
    · simp only [gatherM, pick, packL_cons, ndiv, nmod, nadd, nmul, e1, e2, ih]

theorem pick_small : ∀ (bs : List Bool) (xs : List ℕ), Small xs → Small (pick bs xs)
  | [], _, _ => by intro y hy; simp [pick] at hy
  | _ :: _, [], _ => by intro y hy; simp [pick] at hy
  | true :: bs, x :: xs, h => by
    intro y hy
    simp only [pick, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact h.head
    · exact pick_small bs xs h.tail y hy
  | false :: bs, x :: xs, h => by
    intro y hy
    simp only [pick] at hy
    exact pick_small bs xs h.tail y hy

theorem spreadM_pick : ∀ (bs : List Bool) (xs : List ℕ), Small xs → bs.length = xs.length →
    spreadM bs (packL (pick bs xs)) = packL (zeroOut bs xs)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | b :: bs, x :: xs, hs, hl => by
    have hx := hs.head
    have ih := spreadM_pick bs xs hs.tail (by simpa using hl)
    cases b
    · simp only [spreadM, pick, zeroOut, packL_cons, nmul, ih, zero_add]
    · have e1 : (x + 4 * packL (pick bs xs)) / 4 = packL (pick bs xs) := by omega
      have e2 : (x + 4 * packL (pick bs xs)) % 4 = x := by omega
      simp only [spreadM, pick, zeroOut, packL_cons, ndiv, nmod, nadd, nmul, e1, e2, ih]

theorem land_digit {a b : ℕ} (ha : a < 4) (hb : b < 4) (x y : ℕ) :
    (a + 4 * x) &&& (b + 4 * y) = (a &&& b) + 4 * (x &&& y) := by
  have hab : a &&& b < 2 ^ 2 := Nat.and_lt_two_pow a (by simpa using hb)
  apply Nat.eq_of_testBit_eq
  intro j
  have e1 : a + 4 * x = 2 ^ 2 * x + a := by ring
  have e2 : b + 4 * y = 2 ^ 2 * y + b := by ring
  have e3 : (a &&& b) + 4 * (x &&& y) = 2 ^ 2 * (x &&& y) + (a &&& b) := by ring
  rw [e1, e2, e3, Nat.testBit_and, Nat.testBit_two_pow_mul_add x (by simpa using ha),
    Nat.testBit_two_pow_mul_add y (by simpa using hb), Nat.testBit_two_pow_mul_add _ hab]
  split_ifs <;> simp

theorem land_maskM : ∀ (bs : List Bool) (xs : List ℕ), Small xs → bs.length = xs.length →
    packL xs &&& maskM bs = packL (zeroOut bs xs)
  | [], [], _, _ => by simp [packL, maskM, zeroOut]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | b :: bs, x :: xs, hs, hl => by
    have hx := hs.head
    have ih := land_maskM bs xs hs.tail (by simpa using hl)
    cases b
    · have e : Nat.mul 4 (maskM bs) = 0 + 4 * maskM bs := by rw [zero_add]; rfl
      simp only [maskM, zeroOut, packL_cons, e]
      rw [land_digit hx (by norm_num), ih]
      simp
    · have e : Nat.add 3 (Nat.mul 4 (maskM bs)) = 3 + 4 * maskM bs := rfl
      simp only [maskM, zeroOut, packL_cons, e]
      rw [land_digit hx (by norm_num), ih]
      congr 1
      interval_cases x <;> rfl

/-- Gathering then spreading keeps exactly the trits of the mask. -/
theorem spread_gather (bs : List Bool) (xs : List ℕ) (hs : Small xs) (hl : bs.length = xs.length) :
    spreadM bs (gatherM bs (packL xs)) = packL xs &&& maskM bs := by
  rw [gatherM_packL bs xs hs hl, spreadM_pick bs xs hs hl, land_maskM bs xs hs hl]

theorem compat_test (x A M : ℕ) : ((x &&& M) ^^^ (x &&& A)) &&& (A &&& M) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
  cases x.testBit j <;> cases A.testBit j <;> cases M.testBit j <;> rfl

theorem lor_land (x A M : ℕ) : (x &&& A) ||| (x &&& M) = x &&& (A ||| M) :=
  (Nat.and_or_distrib_left x A M).symm

/-- Trit `k` of a packed list. -/
theorem tr_packL : ∀ (xs : List ℕ) (k : ℕ), Small xs → tr (packL xs) k = xs.getD k 0
  | [], k, _ => by simp [tr, packL, nmod]
  | x :: xs, 0, h => by
    have hx := h.head
    simp only [tr, packL_cons, nmod, nshr, nmul, Nat.mul_zero, Nat.shiftRight_zero,
      List.getD_cons_zero]
    omega
  | x :: xs, k + 1, h => by
    have hx := h.head
    have ih := tr_packL xs k h.tail
    simp only [tr, nmod, nshr, nmul] at ih ⊢
    rw [List.getD_cons_succ, ← ih, packL_cons, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have e : 2 ^ (2 * (k + 1)) = 4 * 2 ^ (2 * k) := by rw [Nat.mul_succ, pow_add]; ring
    rw [e, ← Nat.div_div_eq_div_mul]
    congr 2
    omega

end BeatAvg.K8
