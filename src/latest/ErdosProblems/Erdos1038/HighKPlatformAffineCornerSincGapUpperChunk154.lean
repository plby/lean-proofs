import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk154
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk154
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 154. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_154 : Rat := -505051007121 / 1000000000000

theorem gapUpperCheck_154 : EvalUpper ![qOuter_154, rOuter_154]
    (sincGapE2 scalarTrigDoubles) gapUpper_154 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
