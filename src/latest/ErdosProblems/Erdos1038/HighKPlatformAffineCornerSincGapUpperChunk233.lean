import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk233
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk233
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 233. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_233 : Rat := -467451377690 / 1000000000000

theorem gapUpperCheck_233 : EvalUpper ![qOuter_233, rOuter_233]
    (sincGapE2 scalarTrigDoubles) gapUpper_233 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
