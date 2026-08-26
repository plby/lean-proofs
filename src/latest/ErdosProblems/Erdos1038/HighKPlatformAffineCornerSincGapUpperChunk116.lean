import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk116
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk116
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 116. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_116 : Rat := -519059220775 / 1000000000000

theorem gapUpperCheck_116 : EvalUpper ![qOuter_116, rOuter_116]
    (sincGapE2 scalarTrigDoubles) gapUpper_116 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
