import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk157
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk157
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 157. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_157 : Rat := -503815629549 / 1000000000000

theorem gapUpperCheck_157 : EvalUpper ![qOuter_157, rOuter_157]
    (sincGapE2 scalarTrigDoubles) gapUpper_157 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
