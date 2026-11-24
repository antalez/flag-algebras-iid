import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_92 : Data.endpointOk Data.patterns[92]! = true := by decide +kernel

theorem endpoints_93 : Data.endpointOk Data.patterns[93]! = true := by decide +kernel

theorem endpoints_94 : Data.endpointOk Data.patterns[94]! = true := by decide +kernel

theorem endpoints_95 : Data.endpointOk Data.patterns[95]! = true := by decide +kernel

end Fast.Five.Checked
