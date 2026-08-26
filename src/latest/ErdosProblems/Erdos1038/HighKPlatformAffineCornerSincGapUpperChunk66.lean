import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk66
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk66
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 66. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_066 : Rat := -531901614387 / 1000000000000

theorem gapUpperCheck_066 : EvalUpper ![qOuter_066, rOuter_066]
    (sincGapE2 scalarTrigDoubles) gapUpper_066 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
