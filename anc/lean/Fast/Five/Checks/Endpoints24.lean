import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_96 : Data.endpointOk Data.patterns[96]! = true := by decide +kernel

theorem endpoints_97 : Data.endpointOk Data.patterns[97]! = true := by decide +kernel

theorem endpoints_98 : Data.endpointOk Data.patterns[98]! = true := by decide +kernel

theorem endpoints_99 : Data.endpointOk Data.patterns[99]! = true := by decide +kernel

end Fast.Five.Checked
