import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded5_12 : expandedRow Data.block5 12 = true := by decide +kernel

theorem expanded5_13 : expandedRow Data.block5 13 = true := by decide +kernel

theorem expanded5_14 : expandedRow Data.block5 14 = true := by decide +kernel

theorem expanded5_15 : expandedRow Data.block5 15 = true := by decide +kernel

end Fast.Five.Checked
