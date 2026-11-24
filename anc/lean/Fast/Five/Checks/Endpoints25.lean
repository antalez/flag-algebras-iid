import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_100 : Data.endpointOk Data.patterns[100]! = true := by decide +kernel

theorem endpoints_101 : Data.endpointOk Data.patterns[101]! = true := by decide +kernel

theorem endpoints_102 : Data.endpointOk Data.patterns[102]! = true := by decide +kernel

theorem endpoints_103 : Data.endpointOk Data.patterns[103]! = true := by decide +kernel

end Fast.Five.Checked
