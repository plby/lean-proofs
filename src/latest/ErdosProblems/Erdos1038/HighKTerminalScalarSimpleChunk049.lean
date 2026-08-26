import ErdosProblems.Erdos1038.HighKTerminalScalarData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing terminal simple items 49 through 49. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKTerminalFormula.CertificateData.SimpleChunk049

open Erdos1038.OneCutTailCertificate

def items : List TailQBox :=
  (simpleBoxes.drop 49).take 1

theorem certified : AllSimpleCertified items := by
  kernel_decide

end Erdos1038.HighKTerminalFormula.CertificateData.SimpleChunk049
