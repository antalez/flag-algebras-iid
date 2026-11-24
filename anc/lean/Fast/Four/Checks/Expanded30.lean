import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem expanded3_0 : expandedRow Data.block3 0 = true := by decide +kernel

theorem expanded3_1 : expandedRow Data.block3 1 = true := by decide +kernel

theorem expanded3_2 : expandedRow Data.block3 2 = true := by decide +kernel

theorem expanded3_3 : expandedRow Data.block3 3 = true := by decide +kernel

end Fast.Four.Checked
