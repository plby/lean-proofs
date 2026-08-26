import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk91
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk91
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 91. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_091 : Rat := -526370596045 / 1000000000000

theorem gapUpperCheck_091 : EvalUpper ![qOuter_091, rOuter_091]
    (sincGapE2 scalarTrigDoubles) gapUpper_091 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
