import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_4 : Data.endpointOk Data.patterns[4]! = true := by decide +kernel

theorem endpoints_5 : Data.endpointOk Data.patterns[5]! = true := by decide +kernel

theorem endpoints_6 : Data.endpointOk Data.patterns[6]! = true := by decide +kernel

theorem endpoints_7 : Data.endpointOk Data.patterns[7]! = true := by decide +kernel

end Fast.Five.Checked
