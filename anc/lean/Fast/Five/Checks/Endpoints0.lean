import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_0 : Data.endpointOk Data.patterns[0]! = true := by decide +kernel

theorem endpoints_1 : Data.endpointOk Data.patterns[1]! = true := by decide +kernel

theorem endpoints_2 : Data.endpointOk Data.patterns[2]! = true := by decide +kernel

theorem endpoints_3 : Data.endpointOk Data.patterns[3]! = true := by decide +kernel

end Fast.Five.Checked
