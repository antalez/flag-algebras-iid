import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_136 : Data.endpointOk Data.patterns[136]! = true := by decide +kernel

theorem endpoints_137 : Data.endpointOk Data.patterns[137]! = true := by decide +kernel

theorem endpoints_138 : Data.endpointOk Data.patterns[138]! = true := by decide +kernel

theorem endpoints_139 : Data.endpointOk Data.patterns[139]! = true := by decide +kernel

end Fast.Five.Checked
