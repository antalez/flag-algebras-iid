import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_88 : Data.endpointOk Data.patterns[88]! = true := by decide +kernel

theorem endpoints_89 : Data.endpointOk Data.patterns[89]! = true := by decide +kernel

theorem endpoints_90 : Data.endpointOk Data.patterns[90]! = true := by decide +kernel

theorem endpoints_91 : Data.endpointOk Data.patterns[91]! = true := by decide +kernel

end Fast.Five.Checked
