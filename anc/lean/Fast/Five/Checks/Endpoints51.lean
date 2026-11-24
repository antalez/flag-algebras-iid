import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_204 : Data.endpointOk Data.patterns[204]! = true := by decide +kernel

theorem endpoints_205 : Data.endpointOk Data.patterns[205]! = true := by decide +kernel

theorem endpoints_206 : Data.endpointOk Data.patterns[206]! = true := by decide +kernel

theorem endpoints_207 : Data.endpointOk Data.patterns[207]! = true := by decide +kernel

end Fast.Five.Checked
