import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_20 : Data.endpointOk Data.patterns[20]! = true := by decide +kernel

theorem endpoints_21 : Data.endpointOk Data.patterns[21]! = true := by decide +kernel

theorem endpoints_22 : Data.endpointOk Data.patterns[22]! = true := by decide +kernel

theorem endpoints_23 : Data.endpointOk Data.patterns[23]! = true := by decide +kernel

end Fast.Five.Checked
