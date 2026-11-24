import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_28 : Data.endpointOk Data.patterns[28]! = true := by decide +kernel

theorem endpoints_29 : Data.endpointOk Data.patterns[29]! = true := by decide +kernel

theorem endpoints_30 : Data.endpointOk Data.patterns[30]! = true := by decide +kernel

theorem endpoints_31 : Data.endpointOk Data.patterns[31]! = true := by decide +kernel

end Fast.Five.Checked
