import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded3_20 : expandedRow Data.block3 20 = true := by decide +kernel

theorem expanded3_21 : expandedRow Data.block3 21 = true := by decide +kernel

theorem expanded3_22 : expandedRow Data.block3 22 = true := by decide +kernel

theorem expanded3_23 : expandedRow Data.block3 23 = true := by decide +kernel

end Fast.Five.Checked
