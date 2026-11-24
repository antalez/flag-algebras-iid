import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_120 : Data.endpointOk Data.patterns[120]! = true := by decide +kernel

theorem endpoints_121 : Data.endpointOk Data.patterns[121]! = true := by decide +kernel

theorem endpoints_122 : Data.endpointOk Data.patterns[122]! = true := by decide +kernel

theorem endpoints_123 : Data.endpointOk Data.patterns[123]! = true := by decide +kernel

end Fast.Five.Checked
