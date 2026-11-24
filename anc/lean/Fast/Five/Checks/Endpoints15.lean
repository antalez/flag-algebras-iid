import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_60 : Data.endpointOk Data.patterns[60]! = true := by decide +kernel

theorem endpoints_61 : Data.endpointOk Data.patterns[61]! = true := by decide +kernel

theorem endpoints_62 : Data.endpointOk Data.patterns[62]! = true := by decide +kernel

theorem endpoints_63 : Data.endpointOk Data.patterns[63]! = true := by decide +kernel

end Fast.Five.Checked
