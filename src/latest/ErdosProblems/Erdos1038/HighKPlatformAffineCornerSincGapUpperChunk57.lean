import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk57
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk57
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 57. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_057 : Rat := -533423506499 / 1000000000000

theorem gapUpperCheck_057 : EvalUpper ![qOuter_057, rOuter_057]
    (sincGapE2 scalarTrigDoubles) gapUpper_057 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
