import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded5_0 : expandedRow Data.block5 0 = true := by decide +kernel

theorem expanded5_1 : expandedRow Data.block5 1 = true := by decide +kernel

theorem expanded5_2 : expandedRow Data.block5 2 = true := by decide +kernel

theorem expanded5_3 : expandedRow Data.block5 3 = true := by decide +kernel

end Fast.Five.Checked
