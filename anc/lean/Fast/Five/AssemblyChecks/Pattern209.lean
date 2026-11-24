import Fast.Five.AssembledCheck
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace Fast.Five.AssemblyChecked
theorem pattern209 : assembledOk Data.patterns[209]! = true := by decide +kernel
end Fast.Five.AssemblyChecked
