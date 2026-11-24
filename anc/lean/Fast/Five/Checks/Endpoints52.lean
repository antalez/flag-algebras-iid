import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_208 : Data.endpointOk Data.patterns[208]! = true := by decide +kernel

theorem endpoints_209 : Data.endpointOk Data.patterns[209]! = true := by decide +kernel

theorem endpoints_210 : Data.endpointOk Data.patterns[210]! = true := by decide +kernel

theorem endpoints_211 : Data.endpointOk Data.patterns[211]! = true := by decide +kernel

end Fast.Five.Checked
