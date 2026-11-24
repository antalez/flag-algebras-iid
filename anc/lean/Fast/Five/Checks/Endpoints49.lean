import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_196 : Data.endpointOk Data.patterns[196]! = true := by decide +kernel

theorem endpoints_197 : Data.endpointOk Data.patterns[197]! = true := by decide +kernel

theorem endpoints_198 : Data.endpointOk Data.patterns[198]! = true := by decide +kernel

theorem endpoints_199 : Data.endpointOk Data.patterns[199]! = true := by decide +kernel

end Fast.Five.Checked
