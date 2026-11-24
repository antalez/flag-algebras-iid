import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_64 : Data.endpointOk Data.patterns[64]! = true := by decide +kernel

theorem endpoints_65 : Data.endpointOk Data.patterns[65]! = true := by decide +kernel

theorem endpoints_66 : Data.endpointOk Data.patterns[66]! = true := by decide +kernel

theorem endpoints_67 : Data.endpointOk Data.patterns[67]! = true := by decide +kernel

end Fast.Five.Checked
