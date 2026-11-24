import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_216 : Data.endpointOk Data.patterns[216]! = true := by decide +kernel

theorem endpoints_217 : Data.endpointOk Data.patterns[217]! = true := by decide +kernel

theorem endpoints_218 : Data.endpointOk Data.patterns[218]! = true := by decide +kernel

theorem endpoints_219 : Data.endpointOk Data.patterns[219]! = true := by decide +kernel

end Fast.Five.Checked
