import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_16 : Data.endpointOk Data.patterns[16]! = true := by decide +kernel

theorem endpoints_17 : Data.endpointOk Data.patterns[17]! = true := by decide +kernel

theorem endpoints_18 : Data.endpointOk Data.patterns[18]! = true := by decide +kernel

theorem endpoints_19 : Data.endpointOk Data.patterns[19]! = true := by decide +kernel

end Fast.Five.Checked
