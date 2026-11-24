import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_36 : Data.endpointOk Data.patterns[36]! = true := by decide +kernel

theorem endpoints_37 : Data.endpointOk Data.patterns[37]! = true := by decide +kernel

theorem endpoints_38 : Data.endpointOk Data.patterns[38]! = true := by decide +kernel

theorem endpoints_39 : Data.endpointOk Data.patterns[39]! = true := by decide +kernel

end Fast.Five.Checked
