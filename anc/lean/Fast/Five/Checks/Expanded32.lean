import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded3_8 : expandedRow Data.block3 8 = true := by decide +kernel

theorem expanded3_9 : expandedRow Data.block3 9 = true := by decide +kernel

theorem expanded3_10 : expandedRow Data.block3 10 = true := by decide +kernel

theorem expanded3_11 : expandedRow Data.block3 11 = true := by decide +kernel

end Fast.Five.Checked
