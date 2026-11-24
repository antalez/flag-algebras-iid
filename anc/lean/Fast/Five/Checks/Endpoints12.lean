import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_48 : Data.endpointOk Data.patterns[48]! = true := by decide +kernel

theorem endpoints_49 : Data.endpointOk Data.patterns[49]! = true := by decide +kernel

theorem endpoints_50 : Data.endpointOk Data.patterns[50]! = true := by decide +kernel

theorem endpoints_51 : Data.endpointOk Data.patterns[51]! = true := by decide +kernel

end Fast.Five.Checked
