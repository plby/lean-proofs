import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk206
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk206
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 206. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_206 : Rat := -481390071543 / 1000000000000

theorem gapUpperCheck_206 : EvalUpper ![qOuter_206, rOuter_206]
    (sincGapE2 scalarTrigDoubles) gapUpper_206 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
