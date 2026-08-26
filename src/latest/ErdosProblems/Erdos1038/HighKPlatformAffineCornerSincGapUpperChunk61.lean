import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk61
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk61
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 61. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_061 : Rat := -532778382191 / 1000000000000

theorem gapUpperCheck_061 : EvalUpper ![qOuter_061, rOuter_061]
    (sincGapE2 scalarTrigDoubles) gapUpper_061 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
