import Fast.Five.Arrangements
import Fast.Five.Data

namespace Fast.Five

def assembledOk (p : Pattern) : Bool :=
  keq (assembledScore Data.blocks Data.wHalf Data.wTwice Data.nu p K.bstar)
    (score Data.blocks Data.wHalf Data.wTwice Data.nu p K.bstar) &&
  keq (assembledScore Data.blocks Data.wHalf Data.wTwice Data.nu p K.one)
    (score Data.blocks Data.wHalf Data.wTwice Data.nu p K.one)

end Fast.Five
