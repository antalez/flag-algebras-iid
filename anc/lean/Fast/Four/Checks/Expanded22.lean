import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem expanded2_8 : expandedRow Data.block2 8 = true := by decide +kernel

theorem expanded2_9 : expandedRow Data.block2 9 = true := by decide +kernel

theorem expanded2_10 : expandedRow Data.block2 10 = true := by decide +kernel

theorem expanded2_11 : expandedRow Data.block2 11 = true := by decide +kernel

end Fast.Four.Checked
