import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded3_12 : expandedRow Data.block3 12 = true := by decide +kernel

theorem expanded3_13 : expandedRow Data.block3 13 = true := by decide +kernel

theorem expanded3_14 : expandedRow Data.block3 14 = true := by decide +kernel

theorem expanded3_15 : expandedRow Data.block3 15 = true := by decide +kernel

end Fast.Five.Checked
