import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk234
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk234
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 234. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_234 : Rat := -466916009360 / 1000000000000

theorem gapUpperCheck_234 : EvalUpper ![qOuter_234, rOuter_234]
    (sincGapE2 scalarTrigDoubles) gapUpper_234 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
