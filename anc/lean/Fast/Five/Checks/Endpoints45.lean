import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_180 : Data.endpointOk Data.patterns[180]! = true := by decide +kernel

theorem endpoints_181 : Data.endpointOk Data.patterns[181]! = true := by decide +kernel

theorem endpoints_182 : Data.endpointOk Data.patterns[182]! = true := by decide +kernel

theorem endpoints_183 : Data.endpointOk Data.patterns[183]! = true := by decide +kernel

end Fast.Five.Checked
