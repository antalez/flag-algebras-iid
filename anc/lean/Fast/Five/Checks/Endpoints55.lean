import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_220 : Data.endpointOk Data.patterns[220]! = true := by decide +kernel

theorem endpoints_221 : Data.endpointOk Data.patterns[221]! = true := by decide +kernel

theorem endpoints_222 : Data.endpointOk Data.patterns[222]! = true := by decide +kernel

theorem endpoints_223 : Data.endpointOk Data.patterns[223]! = true := by decide +kernel

end Fast.Five.Checked
