import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_188 : Data.endpointOk Data.patterns[188]! = true := by decide +kernel

theorem endpoints_189 : Data.endpointOk Data.patterns[189]! = true := by decide +kernel

theorem endpoints_190 : Data.endpointOk Data.patterns[190]! = true := by decide +kernel

theorem endpoints_191 : Data.endpointOk Data.patterns[191]! = true := by decide +kernel

end Fast.Five.Checked
