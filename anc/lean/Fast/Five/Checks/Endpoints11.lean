import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_44 : Data.endpointOk Data.patterns[44]! = true := by decide +kernel

theorem endpoints_45 : Data.endpointOk Data.patterns[45]! = true := by decide +kernel

theorem endpoints_46 : Data.endpointOk Data.patterns[46]! = true := by decide +kernel

theorem endpoints_47 : Data.endpointOk Data.patterns[47]! = true := by decide +kernel

end Fast.Five.Checked
