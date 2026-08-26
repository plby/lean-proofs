import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk146
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk146
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 146. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_146 : Rat := -508258443130 / 1000000000000

theorem gapUpperCheck_146 : EvalUpper ![qOuter_146, rOuter_146]
    (sincGapE2 scalarTrigDoubles) gapUpper_146 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
