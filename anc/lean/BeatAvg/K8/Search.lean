/-!
# Kernel-friendly enumeration of patterns (definitions)

Everything here is structural recursion on lists and arithmetic on natural numbers written with the
core functions (`Nat.add`, `Nat.land`, ...), which the kernel evaluates with GMP.

A pattern of `n` sorted points is the list of the trits of its quadruples in the *nested order*
`ordQ n`: quadruples are listed by their largest element first, then lexicographically. So the
pattern of the first `n - 1` points is a prefix of the pattern of `n` points; the remaining trits,
those of the quadruples `(a, b, c, n - 1)`, are the *extension*. A list of trits is packed into a
number, two bits per trit, first trit lowest.
-/

namespace BeatAvg.K8

/-- The triples `a < b < c < m` in lexicographic order. -/
def triples (m : Nat) : List (Nat × Nat × Nat) :=
  (List.range m).flatMap fun a => (List.range m).flatMap fun b => (List.range m).filterMap fun c =>
    if a < b ∧ b < c then some (a, b, c) else none

/-- The quadruples of `n` points in nested order. -/
def ordQ : Nat → List (Nat × Nat × Nat × Nat)
  | 0 => []
  | n + 1 => ordQ n ++ (triples n).map fun t => (t.1, t.2.1, t.2.2, n)

/-- Trit `k` of a packed list. -/
def tr (N k : Nat) : Nat := Nat.mod (Nat.shiftRight N (Nat.mul 2 k)) 4

/-- Pack a list of trits. -/
def packL : List Nat → Nat
  | [] => 0
  | t :: l => Nat.add t (Nat.mul 4 (packL l))

/-- The first `k` trits of a packed list. -/
def unpackL (N : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, p => tr N p :: unpackL N k (p + 1)

/-- The trits whose flag is `true`, packed. -/
def gatherM : List Bool → Nat → Nat
  | [], _ => 0
  | true :: bs, N => Nat.add (Nat.mod N 4) (Nat.mul 4 (gatherM bs (Nat.div N 4)))
  | false :: bs, N => gatherM bs (Nat.div N 4)

/-- Put the trits of `e` at the positions whose flag is `true`. -/
def spreadM : List Bool → Nat → Nat
  | [], _ => 0
  | true :: bs, e => Nat.add (Nat.mod e 4) (Nat.mul 4 (spreadM bs (Nat.div e 4)))
  | false :: bs, e => Nat.mul 4 (spreadM bs e)

/-- All bits of the trits whose flag is `true`. -/
def maskM : List Bool → Nat
  | [] => 0
  | true :: bs => Nat.add 3 (Nat.mul 4 (maskM bs))
  | false :: bs => Nat.mul 4 (maskM bs)

def avoid4 (j : Nat) (q : Nat × Nat × Nat × Nat) : Bool :=
  !(Nat.beq q.1 j) && !(Nat.beq q.2.1 j) && !(Nat.beq q.2.2.1 j) && !(Nat.beq q.2.2.2 j)

def avoid3 (j : Nat) (t : Nat × Nat × Nat) : Bool :=
  !(Nat.beq t.1 j) && !(Nat.beq t.2.1 j) && !(Nat.beq t.2.2 j)

/-- The quadruples of the pattern of `m` points that avoid the point `j`. -/
def avoidQ (m j : Nat) : List Bool := (ordQ m).map (avoid4 j)

/-- The triples of the extension of a pattern of `m` points that avoid the point `j`. -/
def avoidT (m j : Nat) : List Bool := (triples m).map (avoid3 j)

/-- A level grouped by prefix: `(code of the prefix, number of extensions, packed extensions)`. -/
abbrev Grouped := List (Nat × Nat × Nat)

def lookupG : Grouped → Nat → Nat × Nat
  | [], _ => (0, 0)
  | g :: gs, key => bif Nat.beq g.1 key then g.2 else lookupG gs key

/-- `c` fields of `w` bits. -/
def unpackE (w : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | c + 1, x => Nat.mod x (Nat.pow 2 w) :: unpackE w c (Nat.shiftRight x w)

/-- The extensions allowed by the restriction that deletes the point `j`: those of the pattern of
the other `m - 1` points among the first `m`, spread to the positions of the triples avoiding `j`.
`G` is the level of `m` points, `w` the number of bits of its extensions. -/
def candsJ (G : Grouped) (w m T j : Nat) : List Nat :=
  (unpackE w (lookupG G (gatherM (avoidQ m j) T)).1 (lookupG G (gatherM (avoidQ m j) T)).2).map
    (spreadM (avoidT m j))

/-- The candidates of a stage that agree with the partial extension `V` on the bits `O`. -/
def ext1 (O V : Nat) : List Nat → List Nat
  | [] => []
  | e :: l => bif Nat.beq (Nat.land (Nat.xor e V) O) 0 then Nat.lor V e :: ext1 O V l else ext1 O V l

def extAll (O : Nat) (E : List Nat) : List Nat → List Nat
  | [] => []
  | V :: l => ext1 O V E ++ extAll O E l

/-- Stages `j, j + 1, ...` (`f` of them); `A` is the set of bits assigned so far. -/
def joinFrom (G : Grouped) (w m T : Nat) : Nat → Nat → Nat → List Nat → List Nat
  | 0, _, _, st => st
  | f + 1, j, A, st =>
    joinFrom G w m T f (j + 1) (Nat.lor A (maskM (avoidT m j)))
      (extAll (Nat.land A (maskM (avoidT m j))) (candsJ G w m T j) st)

/-- The extensions of the pattern `T` of `m` points, all of whose restrictions lie in `G`; only
the candidates `lo ≤ i < hi` of the first stage are followed. -/
def extsR (G : Grouped) (w m T lo hi : Nat) : List Nat :=
  joinFrom G w m T (m - 1) 1 (maskM (avoidT m 0))
    (((candsJ G w m T 0).drop lo).take (hi - lo))

end BeatAvg.K8

namespace BeatAvg.K8

/-! ### The join with the candidates of a stage indexed by a ternary trie

At a stage, a state `V` is compatible with a candidate `e` iff they have the same trits on the
positions assigned both by the stage and by an earlier one. The candidates are sorted into a trie
by their trits on these positions, and each state looks up its leaf instead of testing every
candidate.
-/

inductive Trie where
  | leaf (l : List Nat)
  | node (a b c : Trie)

/-- The candidates with trit `t` at position `p`. -/
def withTrit (p t : Nat) : List Nat → List Nat
  | [] => []
  | e :: l => bif Nat.beq (tr e p) t then e :: withTrit p t l else withTrit p t l

def trieBuild : List Nat → List Nat → Trie
  | [], E => .leaf E
  | p :: ps, E => .node (trieBuild ps (withTrit p 0 E)) (trieBuild ps (withTrit p 1 E))
      (trieBuild ps (withTrit p 2 E))

def trieFind : Trie → List Nat → Nat → List Nat
  | .leaf l, _, _ => l
  | .node a b c, p :: ps, V =>
    bif Nat.beq (tr V p) 0 then trieFind a ps V
    else bif Nat.beq (tr V p) 1 then trieFind b ps V
    else bif Nat.beq (tr V p) 2 then trieFind c ps V else []
  | .node _ _ _, [], _ => []

/-- The trit positions (below `k`) where both `A` and `M` are set. -/
def ovl (k A M : Nat) : List Nat := (List.range k).filter fun p => !(Nat.beq (tr (Nat.land A M) p) 0)

def extAllT (t : Trie) (ps : List Nat) : List Nat → List Nat
  | [] => []
  | V :: l => (trieFind t ps V).map (Nat.lor V) ++ extAllT t ps l

/-- The stages `j, j + 1, ...` with tries. -/
def joinFromT (G : Grouped) (wb m T : Nat) : Nat → Nat → Nat → List Nat → List Nat
  | 0, _, _, st => st
  | f + 1, j, A, st =>
    joinFromT G wb m T f (j + 1) (Nat.lor A (maskM (avoidT m j)))
      (extAllT (trieBuild (ovl (triples m).length A (maskM (avoidT m j))) (candsJ G wb m T j))
        (ovl (triples m).length A (maskM (avoidT m j))) st)

end BeatAvg.K8
