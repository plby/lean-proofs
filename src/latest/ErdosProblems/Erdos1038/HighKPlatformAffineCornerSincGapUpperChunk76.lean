import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk76
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk76
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 76. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_076 : Rat := -529915530976 / 1000000000000

theorem gapUpperCheck_076 : EvalUpper ![qOuter_076, rOuter_076]
    (sincGapE2 scalarTrigDoubles) gapUpper_076 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
