import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_84 : Data.endpointOk Data.patterns[84]! = true := by decide +kernel

theorem endpoints_85 : Data.endpointOk Data.patterns[85]! = true := by decide +kernel

theorem endpoints_86 : Data.endpointOk Data.patterns[86]! = true := by decide +kernel

theorem endpoints_87 : Data.endpointOk Data.patterns[87]! = true := by decide +kernel

end Fast.Five.Checked
