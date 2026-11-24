import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_168 : Data.endpointOk Data.patterns[168]! = true := by decide +kernel

theorem endpoints_169 : Data.endpointOk Data.patterns[169]! = true := by decide +kernel

theorem endpoints_170 : Data.endpointOk Data.patterns[170]! = true := by decide +kernel

theorem endpoints_171 : Data.endpointOk Data.patterns[171]! = true := by decide +kernel

end Fast.Five.Checked
