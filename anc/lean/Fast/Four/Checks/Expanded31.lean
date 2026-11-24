import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem expanded3_4 : expandedRow Data.block3 4 = true := by decide +kernel

theorem expanded3_5 : expandedRow Data.block3 5 = true := by decide +kernel

theorem expanded3_6 : expandedRow Data.block3 6 = true := by decide +kernel

theorem expanded3_7 : expandedRow Data.block3 7 = true := by decide +kernel

end Fast.Four.Checked
