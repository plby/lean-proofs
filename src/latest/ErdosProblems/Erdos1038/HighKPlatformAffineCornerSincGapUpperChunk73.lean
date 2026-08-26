import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk73
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk73
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 73. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_073 : Rat := -530543647544 / 1000000000000

theorem gapUpperCheck_073 : EvalUpper ![qOuter_073, rOuter_073]
    (sincGapE2 scalarTrigDoubles) gapUpper_073 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
