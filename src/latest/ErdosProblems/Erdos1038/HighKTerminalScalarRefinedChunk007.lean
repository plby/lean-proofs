import ErdosProblems.Erdos1038.HighKTerminalScalarData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing terminal refined items 7 through 7. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk007

open Erdos1038.OneCutTailCertificate

def items : List RefinedData :=
  (refinedData.drop 7).take 1

theorem certified : AllRefinedCertified items := by
  kernel_decide

end Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk007
