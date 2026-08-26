import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk236
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk236
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 236. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_236 : Rat := -465841341106 / 1000000000000

theorem gapUpperCheck_236 : EvalUpper ![qOuter_236, rOuter_236]
    (sincGapE2 scalarTrigDoubles) gapUpper_236 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
