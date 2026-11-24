import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded4_0 : expandedRow Data.block4 0 = true := by decide +kernel

theorem expanded4_1 : expandedRow Data.block4 1 = true := by decide +kernel

theorem expanded4_2 : expandedRow Data.block4 2 = true := by decide +kernel

theorem expanded4_3 : expandedRow Data.block4 3 = true := by decide +kernel

end Fast.Five.Checked
