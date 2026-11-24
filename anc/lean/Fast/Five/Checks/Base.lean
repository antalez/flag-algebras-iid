import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem enclosure : enclosureOk Data.encLo Data.encHi Data.encM = true := by decide +kernel

theorem shape0 : blockShape Data.block0 = true := by decide +kernel

theorem shape1 : blockShape Data.block1 = true := by decide +kernel

theorem shape2 : blockShape Data.block2 = true := by decide +kernel

theorem shape3 : blockShape Data.block3 = true := by decide +kernel

theorem shape4 : blockShape Data.block4 = true := by decide +kernel

theorem shape5 : blockShape Data.block5 = true := by decide +kernel

end Fast.Five.Checked
