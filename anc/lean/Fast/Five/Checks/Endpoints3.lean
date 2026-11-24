import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_12 : Data.endpointOk Data.patterns[12]! = true := by decide +kernel

theorem endpoints_13 : Data.endpointOk Data.patterns[13]! = true := by decide +kernel

theorem endpoints_14 : Data.endpointOk Data.patterns[14]! = true := by decide +kernel

theorem endpoints_15 : Data.endpointOk Data.patterns[15]! = true := by decide +kernel

end Fast.Five.Checked
