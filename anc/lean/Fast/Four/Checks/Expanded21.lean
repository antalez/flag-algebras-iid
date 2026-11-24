import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem expanded2_4 : expandedRow Data.block2 4 = true := by decide +kernel

theorem expanded2_5 : expandedRow Data.block2 5 = true := by decide +kernel

theorem expanded2_6 : expandedRow Data.block2 6 = true := by decide +kernel

theorem expanded2_7 : expandedRow Data.block2 7 = true := by decide +kernel

end Fast.Four.Checked
