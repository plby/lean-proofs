import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk208
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk208
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 208. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_208 : Rat := -480393010471 / 1000000000000

theorem gapUpperCheck_208 : EvalUpper ![qOuter_208, rOuter_208]
    (sincGapE2 scalarTrigDoubles) gapUpper_208 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
