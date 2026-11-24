import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_148 : Data.endpointOk Data.patterns[148]! = true := by decide +kernel

theorem endpoints_149 : Data.endpointOk Data.patterns[149]! = true := by decide +kernel

theorem endpoints_150 : Data.endpointOk Data.patterns[150]! = true := by decide +kernel

theorem endpoints_151 : Data.endpointOk Data.patterns[151]! = true := by decide +kernel

end Fast.Five.Checked
