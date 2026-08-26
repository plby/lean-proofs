import ErdosProblems.Erdos1038.TaoUpperCaseOneCertificateData
import ErdosProblems.Erdos1038.KernelDecision

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038

theorem taoCaseOneDirectChunk29_certify :
    (taoCaseOneDirectIntervals.drop 580).all (taoCaseOneGapPositive 100) = true := by
  kernel_decide

end Erdos1038

