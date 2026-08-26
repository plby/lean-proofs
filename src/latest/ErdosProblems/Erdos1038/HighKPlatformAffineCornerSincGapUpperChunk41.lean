import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk41
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk41
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 41. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_041 : Rat := -535504652075 / 1000000000000

theorem gapUpperCheck_041 : EvalUpper ![qOuter_041, rOuter_041]
    (sincGapE2 scalarTrigDoubles) gapUpper_041 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
