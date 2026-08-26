import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk260
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk260
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 260. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_260 : Rat := -452550311205 / 1000000000000

theorem gapUpperCheck_260 : EvalUpper ![qOuter_260, rOuter_260]
    (sincGapE2 scalarTrigDoubles) gapUpper_260 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
