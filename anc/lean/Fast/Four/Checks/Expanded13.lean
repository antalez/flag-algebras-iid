import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem expanded1_12 : expandedRow Data.block1 12 = true := by decide +kernel

theorem expanded1_13 : expandedRow Data.block1 13 = true := by decide +kernel

theorem expanded1_14 : expandedRow Data.block1 14 = true := by decide +kernel

theorem expanded1_15 : expandedRow Data.block1 15 = true := by decide +kernel

end Fast.Four.Checked
