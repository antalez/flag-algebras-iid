import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_200 : Data.endpointOk Data.patterns[200]! = true := by decide +kernel

theorem endpoints_201 : Data.endpointOk Data.patterns[201]! = true := by decide +kernel

theorem endpoints_202 : Data.endpointOk Data.patterns[202]! = true := by decide +kernel

theorem endpoints_203 : Data.endpointOk Data.patterns[203]! = true := by decide +kernel

end Fast.Five.Checked
