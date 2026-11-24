import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_284 : Data.endpointOk Data.patterns[284]! = true := by decide +kernel

theorem endpoints_285 : Data.endpointOk Data.patterns[285]! = true := by decide +kernel

theorem endpoints_286 : Data.endpointOk Data.patterns[286]! = true := by decide +kernel

theorem endpoints_287 : Data.endpointOk Data.patterns[287]! = true := by decide +kernel

end Fast.Five.Checked
