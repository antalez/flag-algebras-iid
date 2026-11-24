import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded5_8 : expandedRow Data.block5 8 = true := by decide +kernel

theorem expanded5_9 : expandedRow Data.block5 9 = true := by decide +kernel

theorem expanded5_10 : expandedRow Data.block5 10 = true := by decide +kernel

theorem expanded5_11 : expandedRow Data.block5 11 = true := by decide +kernel

end Fast.Five.Checked
