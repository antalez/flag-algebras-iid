import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_232 : Data.endpointOk Data.patterns[232]! = true := by decide +kernel

theorem endpoints_233 : Data.endpointOk Data.patterns[233]! = true := by decide +kernel

theorem endpoints_234 : Data.endpointOk Data.patterns[234]! = true := by decide +kernel

theorem endpoints_235 : Data.endpointOk Data.patterns[235]! = true := by decide +kernel

end Fast.Five.Checked
