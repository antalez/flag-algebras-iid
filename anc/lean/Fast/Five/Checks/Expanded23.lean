import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded2_12 : expandedRow Data.block2 12 = true := by decide +kernel

theorem expanded2_13 : expandedRow Data.block2 13 = true := by decide +kernel

theorem expanded2_14 : expandedRow Data.block2 14 = true := by decide +kernel

end Fast.Five.Checked
