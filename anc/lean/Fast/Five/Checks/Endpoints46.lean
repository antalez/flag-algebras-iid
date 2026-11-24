import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_184 : Data.endpointOk Data.patterns[184]! = true := by decide +kernel

theorem endpoints_185 : Data.endpointOk Data.patterns[185]! = true := by decide +kernel

theorem endpoints_186 : Data.endpointOk Data.patterns[186]! = true := by decide +kernel

theorem endpoints_187 : Data.endpointOk Data.patterns[187]! = true := by decide +kernel

end Fast.Five.Checked
