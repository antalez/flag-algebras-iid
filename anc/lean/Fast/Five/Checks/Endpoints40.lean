import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_160 : Data.endpointOk Data.patterns[160]! = true := by decide +kernel

theorem endpoints_161 : Data.endpointOk Data.patterns[161]! = true := by decide +kernel

theorem endpoints_162 : Data.endpointOk Data.patterns[162]! = true := by decide +kernel

theorem endpoints_163 : Data.endpointOk Data.patterns[163]! = true := by decide +kernel

end Fast.Five.Checked
