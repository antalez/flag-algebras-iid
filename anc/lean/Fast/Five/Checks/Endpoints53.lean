import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_212 : Data.endpointOk Data.patterns[212]! = true := by decide +kernel

theorem endpoints_213 : Data.endpointOk Data.patterns[213]! = true := by decide +kernel

theorem endpoints_214 : Data.endpointOk Data.patterns[214]! = true := by decide +kernel

theorem endpoints_215 : Data.endpointOk Data.patterns[215]! = true := by decide +kernel

end Fast.Five.Checked
