import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_8 : Data.endpointOk Data.patterns[8]! = true := by decide +kernel

theorem endpoints_9 : Data.endpointOk Data.patterns[9]! = true := by decide +kernel

theorem endpoints_10 : Data.endpointOk Data.patterns[10]! = true := by decide +kernel

theorem endpoints_11 : Data.endpointOk Data.patterns[11]! = true := by decide +kernel

end Fast.Five.Checked
