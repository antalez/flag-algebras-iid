import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded5_16 : expandedRow Data.block5 16 = true := by decide +kernel

theorem expanded5_17 : expandedRow Data.block5 17 = true := by decide +kernel

theorem expanded5_18 : expandedRow Data.block5 18 = true := by decide +kernel

theorem expanded5_19 : expandedRow Data.block5 19 = true := by decide +kernel

end Fast.Five.Checked
