import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk67
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk67
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 67. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_067 : Rat := -531716908882 / 1000000000000

theorem gapUpperCheck_067 : EvalUpper ![qOuter_067, rOuter_067]
    (sincGapE2 scalarTrigDoubles) gapUpper_067 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
