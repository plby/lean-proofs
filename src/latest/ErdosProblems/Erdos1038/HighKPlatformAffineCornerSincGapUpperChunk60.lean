import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk60
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk60
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 60. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_060 : Rat := -532944360436 / 1000000000000

theorem gapUpperCheck_060 : EvalUpper ![qOuter_060, rOuter_060]
    (sincGapE2 scalarTrigDoubles) gapUpper_060 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
