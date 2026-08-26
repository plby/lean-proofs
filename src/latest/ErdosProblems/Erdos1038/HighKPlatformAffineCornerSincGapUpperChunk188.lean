import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk188
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk188
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 188. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_188 : Rat := -490090387685 / 1000000000000

theorem gapUpperCheck_188 : EvalUpper ![qOuter_188, rOuter_188]
    (sincGapE2 scalarTrigDoubles) gapUpper_188 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
