import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk209
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk209
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 209. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_209 : Rat := -479892278430 / 1000000000000

theorem gapUpperCheck_209 : EvalUpper ![qOuter_209, rOuter_209]
    (sincGapE2 scalarTrigDoubles) gapUpper_209 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
