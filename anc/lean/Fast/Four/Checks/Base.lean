import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem enclosure : enclosureOk Data.encLo Data.encHi Data.encM = true := by decide +kernel

theorem shape0 : blockShape Data.block0 = true := by decide +kernel

theorem shape1 : blockShape Data.block1 = true := by decide +kernel

theorem shape2 : blockShape Data.block2 = true := by decide +kernel

theorem shape3 : blockShape Data.block3 = true := by decide +kernel

end Fast.Four.Checked
