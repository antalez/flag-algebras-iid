import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_32 : Data.endpointOk Data.patterns[32]! = true := by decide +kernel

theorem endpoints_33 : Data.endpointOk Data.patterns[33]! = true := by decide +kernel

theorem endpoints_34 : Data.endpointOk Data.patterns[34]! = true := by decide +kernel

theorem endpoints_35 : Data.endpointOk Data.patterns[35]! = true := by decide +kernel

end Fast.Five.Checked
