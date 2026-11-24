import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_228 : Data.endpointOk Data.patterns[228]! = true := by decide +kernel

theorem endpoints_229 : Data.endpointOk Data.patterns[229]! = true := by decide +kernel

theorem endpoints_230 : Data.endpointOk Data.patterns[230]! = true := by decide +kernel

theorem endpoints_231 : Data.endpointOk Data.patterns[231]! = true := by decide +kernel

end Fast.Five.Checked
