import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk165
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk165
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 165. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_165 : Rat := -500437627201 / 1000000000000

theorem gapUpperCheck_165 : EvalUpper ![qOuter_165, rOuter_165]
    (sincGapE2 scalarTrigDoubles) gapUpper_165 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
