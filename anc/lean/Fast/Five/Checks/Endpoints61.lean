import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_244 : Data.endpointOk Data.patterns[244]! = true := by decide +kernel

theorem endpoints_245 : Data.endpointOk Data.patterns[245]! = true := by decide +kernel

theorem endpoints_246 : Data.endpointOk Data.patterns[246]! = true := by decide +kernel

theorem endpoints_247 : Data.endpointOk Data.patterns[247]! = true := by decide +kernel

end Fast.Five.Checked
