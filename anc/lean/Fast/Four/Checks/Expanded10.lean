import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem expanded1_0 : expandedRow Data.block1 0 = true := by decide +kernel

theorem expanded1_1 : expandedRow Data.block1 1 = true := by decide +kernel

theorem expanded1_2 : expandedRow Data.block1 2 = true := by decide +kernel

theorem expanded1_3 : expandedRow Data.block1 3 = true := by decide +kernel

end Fast.Four.Checked
