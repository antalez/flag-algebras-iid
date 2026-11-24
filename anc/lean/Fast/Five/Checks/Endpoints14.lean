import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_56 : Data.endpointOk Data.patterns[56]! = true := by decide +kernel

theorem endpoints_57 : Data.endpointOk Data.patterns[57]! = true := by decide +kernel

theorem endpoints_58 : Data.endpointOk Data.patterns[58]! = true := by decide +kernel

theorem endpoints_59 : Data.endpointOk Data.patterns[59]! = true := by decide +kernel

end Fast.Five.Checked
