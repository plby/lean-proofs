import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk99
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk99
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 99. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_099 : Rat := -524214258928 / 1000000000000

theorem gapUpperCheck_099 : EvalUpper ![qOuter_099, rOuter_099]
    (sincGapE2 scalarTrigDoubles) gapUpper_099 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
