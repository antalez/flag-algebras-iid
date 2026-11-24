import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded5_4 : expandedRow Data.block5 4 = true := by decide +kernel

theorem expanded5_5 : expandedRow Data.block5 5 = true := by decide +kernel

theorem expanded5_6 : expandedRow Data.block5 6 = true := by decide +kernel

theorem expanded5_7 : expandedRow Data.block5 7 = true := by decide +kernel

end Fast.Five.Checked
