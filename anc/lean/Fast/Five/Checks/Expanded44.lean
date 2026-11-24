import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded4_16 : expandedRow Data.block4 16 = true := by decide +kernel

theorem expanded4_17 : expandedRow Data.block4 17 = true := by decide +kernel

theorem expanded4_18 : expandedRow Data.block4 18 = true := by decide +kernel

end Fast.Five.Checked
