import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk45
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk45
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 45. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_045 : Rat := -535058798559 / 1000000000000

theorem gapUpperCheck_045 : EvalUpper ![qOuter_045, rOuter_045]
    (sincGapE2 scalarTrigDoubles) gapUpper_045 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
