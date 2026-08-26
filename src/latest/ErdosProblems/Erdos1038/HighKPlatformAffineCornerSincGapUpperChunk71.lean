import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk71
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk71
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 71. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_071 : Rat := -530947078269 / 1000000000000

theorem gapUpperCheck_071 : EvalUpper ![qOuter_071, rOuter_071]
    (sincGapE2 scalarTrigDoubles) gapUpper_071 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
