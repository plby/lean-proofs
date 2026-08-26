import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk226
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk226
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 226. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_226 : Rat := -471161780306 / 1000000000000

theorem gapUpperCheck_226 : EvalUpper ![qOuter_226, rOuter_226]
    (sincGapE2 scalarTrigDoubles) gapUpper_226 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
