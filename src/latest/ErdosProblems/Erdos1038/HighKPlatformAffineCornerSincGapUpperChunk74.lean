import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk74
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk74
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 74. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_074 : Rat := -530337329418 / 1000000000000

theorem gapUpperCheck_074 : EvalUpper ![qOuter_074, rOuter_074]
    (sincGapE2 scalarTrigDoubles) gapUpper_074 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
