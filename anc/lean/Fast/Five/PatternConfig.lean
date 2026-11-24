import Fast.Five.FlagCodes
import Fast.Gen

namespace Fast.Five

def quadIndex (a b c d : Nat) : Nat := (quads 5).idxOf [a,b,c,d]

def additiveTrits (p : Pattern) : Array Nat := ((quads 5).map (wins p)).toArray

def patternConfig (p : Pattern) : Config 5 :=
  ⟨Fast.cfgOfPatG 5 quadIndex (additiveTrits p),
    fun i j => decide (i ≠ j) && edge p (min i.val j.val) (max i.val j.val)⟩

end Fast.Five
