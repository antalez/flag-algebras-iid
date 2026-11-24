import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_132 : Data.endpointOk Data.patterns[132]! = true := by decide +kernel

theorem endpoints_133 : Data.endpointOk Data.patterns[133]! = true := by decide +kernel

theorem endpoints_134 : Data.endpointOk Data.patterns[134]! = true := by decide +kernel

theorem endpoints_135 : Data.endpointOk Data.patterns[135]! = true := by decide +kernel

end Fast.Five.Checked
