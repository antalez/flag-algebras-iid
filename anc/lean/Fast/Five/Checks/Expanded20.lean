import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded2_0 : expandedRow Data.block2 0 = true := by decide +kernel

theorem expanded2_1 : expandedRow Data.block2 1 = true := by decide +kernel

theorem expanded2_2 : expandedRow Data.block2 2 = true := by decide +kernel

theorem expanded2_3 : expandedRow Data.block2 3 = true := by decide +kernel

end Fast.Five.Checked
