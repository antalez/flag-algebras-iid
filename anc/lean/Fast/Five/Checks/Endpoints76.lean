import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_304 : Data.endpointOk Data.patterns[304]! = true := by decide +kernel

theorem endpoints_305 : Data.endpointOk Data.patterns[305]! = true := by decide +kernel

theorem endpoints_306 : Data.endpointOk Data.patterns[306]! = true := by decide +kernel

end Fast.Five.Checked
