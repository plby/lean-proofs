import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk254
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk254
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 254. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_254 : Rat := -455939754090 / 1000000000000

theorem gapUpperCheck_254 : EvalUpper ![qOuter_254, rOuter_254]
    (sincGapE2 scalarTrigDoubles) gapUpper_254 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
