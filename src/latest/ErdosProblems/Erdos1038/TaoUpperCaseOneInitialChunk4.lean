import ErdosProblems.Erdos1038.TaoUpperCaseOneCertificateData
import ErdosProblems.Erdos1038.KernelDecision

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038

theorem taoCaseOneInitialChunk4_certify :
    (taoCaseOneInitialIntervals.drop 80).all (taoCaseOneSecondDerivativePositive 80) = true := by
  kernel_decide

end Erdos1038

