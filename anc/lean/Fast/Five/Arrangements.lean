import Fast.Five.PatternConfig
import Fast.Canon

namespace Fast.Five

def fn5 (l : List (Fin 5)) : Fin 5 → Fin 5 := fun i => l.getD i.val 0

def all5 : List (List (Fin 5)) := Fast.allOrders (List.finRange 5)

def reps1 : List (List (Fin 5)) := all5.filter fun l =>
  decide (fn5 l 1 < fn5 l 2 ∧ fn5 l 3 < fn5 l 4)

def reps3 : List (List (Fin 5)) := all5.filter fun l =>
  decide (fn5 l 0 < fn5 l 1 ∧ fn5 l 1 < fn5 l 2)

def restrictConfig {m n : Nat} (c : Config n) (e : Fin m → Fin n) : Config m :=
  ⟨c.additive.comap e, fun i j => c.close (e i) (e j)⟩

def sel13 : Fin 3 → Fin 5 := fun i => ⟨i.val, by omega⟩
def sel13' : Fin 3 → Fin 5 := fun i => if i.val = 0 then 0 else ⟨i.val+2, by omega⟩
def sel34 : Fin 4 → Fin 5 := fun i => ⟨i.val, by omega⟩
def sel34' : Fin 4 → Fin 5 := fun i => if i.val < 3 then ⟨i.val, by omega⟩ else 4

def square1Code (b : Block) (c : Config 5) : K :=
  (ksum (reps1.map fun l => entryAt b.expanded
    (singletonFlag b (restrictConfig c (fn5 l ∘ sel13)) % (b.flags.size+1))
    (singletonFlag b (restrictConfig c (fn5 l ∘ sel13')) % (b.flags.size+1)))).smul (1/30)

def square3Code (b : Block) (c : Config 5) : K :=
  (ksum (reps3.map fun l => entryAt b.expanded
    (tripleFlag b (restrictConfig c (fn5 l ∘ sel34)) % (b.flags.size+1))
    (tripleFlag b (restrictConfig c (fn5 l ∘ sel34')) % (b.flags.size+1)))).smul (1/20)

/-- Objective, degree, and sublaw terms for one ordering, before averaging. -/
def scalarCode (blocks : Array Block) (wH wT : Rat) (nu : Array Rat)
    (c : Config 5) (ρ : Fin 5 → Fin 5) (x : K) : K :=
  let obj := K.ofRat (bitNat (c.additive.sb (ρ 0) (ρ 1) (ρ 2) (ρ 3)))
  let cl := (if c.close (ρ 0) (ρ 1) then 2 else 0) +
    (if c.additive.lt (ρ 0) (ρ 1) then 0 else 1)
  let s := 3*bitNat (c.additive.sb (ρ 0) (ρ 2) (ρ 3) (ρ 4)) +
    bitNat (c.additive.sb (ρ 2) (ρ 3) (ρ 4) (ρ 0))
  let deg := ((K.ofRat ((s : Rat)/4)).sub K.bstar).smul (nu[cl]?.getD 0)
  let half := [1,2,3,4].all fun i => c.additive.lt (ρ i) (ρ 0) && !(c.close (ρ i) (ρ 0))
  let twice := [1,2,3,4].all fun i => c.additive.lt (ρ i) (ρ 0) || c.close (ρ i) (ρ 0)
  let good := c.additive.sb (ρ 1) (ρ 2) (ρ 3) (ρ 4)
  let h := if half then (x.sub (K.ofRat (bitNat good))).smul wH else K.zero
  let t := if twice then (x.sub (K.ofRat (bitNat good))).smul wT else K.zero
  obj.add (deg.add (h.add t))

def assembledScore (blocks : Array Block) (wH wT : Rat) (nu : Array Rat)
    (p : Pattern) (x : K) : K :=
  let c := patternConfig p
  (ksum (all5.map fun l => scalarCode blocks wH wT nu c (fn5 l) x)).smul (1/120) |>.add
    ((square1Code (blocks[0]?.getD default) c).add
      (ksum ((List.range 5).map fun i => square3Code (blocks[i+1]?.getD default) c)))

end Fast.Five
