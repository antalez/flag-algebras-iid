import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded4_12 : expandedRow Data.block4 12 = true := by decide +kernel

theorem expanded4_13 : expandedRow Data.block4 13 = true := by decide +kernel

theorem expanded4_14 : expandedRow Data.block4 14 = true := by decide +kernel

theorem expanded4_15 : expandedRow Data.block4 15 = true := by decide +kernel

end Fast.Five.Checked
