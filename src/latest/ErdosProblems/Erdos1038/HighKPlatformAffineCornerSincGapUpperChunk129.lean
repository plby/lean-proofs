import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk129
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk129
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 129. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_129 : Rat := -514629435105 / 1000000000000

theorem gapUpperCheck_129 : EvalUpper ![qOuter_129, rOuter_129]
    (sincGapE2 scalarTrigDoubles) gapUpper_129 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
