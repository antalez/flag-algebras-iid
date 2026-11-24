import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_240 : Data.endpointOk Data.patterns[240]! = true := by decide +kernel

theorem endpoints_241 : Data.endpointOk Data.patterns[241]! = true := by decide +kernel

theorem endpoints_242 : Data.endpointOk Data.patterns[242]! = true := by decide +kernel

theorem endpoints_243 : Data.endpointOk Data.patterns[243]! = true := by decide +kernel

end Fast.Five.Checked
