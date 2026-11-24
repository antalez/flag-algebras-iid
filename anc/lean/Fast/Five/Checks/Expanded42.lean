import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded4_8 : expandedRow Data.block4 8 = true := by decide +kernel

theorem expanded4_9 : expandedRow Data.block4 9 = true := by decide +kernel

theorem expanded4_10 : expandedRow Data.block4 10 = true := by decide +kernel

theorem expanded4_11 : expandedRow Data.block4 11 = true := by decide +kernel

end Fast.Five.Checked
