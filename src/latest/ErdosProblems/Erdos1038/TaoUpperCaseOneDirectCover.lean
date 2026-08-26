import ErdosProblems.Erdos1038.TaoUpperCaseOneCertificateData
import ErdosProblems.Erdos1038.KernelDecision

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038

theorem taoCaseOneDirectIntervals_cover :
    ratIntervalChainCovers (3 / 2) (2203 / 1250)
      taoCaseOneDirectIntervals = true := by
  kernel_decide

end Erdos1038
