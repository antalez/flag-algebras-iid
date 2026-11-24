import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem expanded1_16 : expandedRow Data.block1 16 = true := by decide +kernel

theorem expanded1_17 : expandedRow Data.block1 17 = true := by decide +kernel

theorem expanded1_18 : expandedRow Data.block1 18 = true := by decide +kernel

theorem expanded1_19 : expandedRow Data.block1 19 = true := by decide +kernel

end Fast.Four.Checked
