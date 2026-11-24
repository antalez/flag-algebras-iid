import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_192 : Data.endpointOk Data.patterns[192]! = true := by decide +kernel

theorem endpoints_193 : Data.endpointOk Data.patterns[193]! = true := by decide +kernel

theorem endpoints_194 : Data.endpointOk Data.patterns[194]! = true := by decide +kernel

theorem endpoints_195 : Data.endpointOk Data.patterns[195]! = true := by decide +kernel

end Fast.Five.Checked
