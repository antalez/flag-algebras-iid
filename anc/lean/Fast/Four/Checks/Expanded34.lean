import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem expanded3_16 : expandedRow Data.block3 16 = true := by decide +kernel

theorem expanded3_17 : expandedRow Data.block3 17 = true := by decide +kernel

theorem expanded3_18 : expandedRow Data.block3 18 = true := by decide +kernel

theorem expanded3_19 : expandedRow Data.block3 19 = true := by decide +kernel

end Fast.Four.Checked
