import Fast.Five.AssembledCheck
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace Fast.Five.AssemblyChecked
theorem pattern103 : assembledOk Data.patterns[103]! = true := by decide +kernel
end Fast.Five.AssemblyChecked
