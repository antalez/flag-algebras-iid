import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded3_24 : expandedRow Data.block3 24 = true := by decide +kernel

theorem expanded3_25 : expandedRow Data.block3 25 = true := by decide +kernel

theorem expanded3_26 : expandedRow Data.block3 26 = true := by decide +kernel

end Fast.Five.Checked
