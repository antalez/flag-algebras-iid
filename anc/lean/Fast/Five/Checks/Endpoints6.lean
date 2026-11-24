import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_24 : Data.endpointOk Data.patterns[24]! = true := by decide +kernel

theorem endpoints_25 : Data.endpointOk Data.patterns[25]! = true := by decide +kernel

theorem endpoints_26 : Data.endpointOk Data.patterns[26]! = true := by decide +kernel

theorem endpoints_27 : Data.endpointOk Data.patterns[27]! = true := by decide +kernel

end Fast.Five.Checked
