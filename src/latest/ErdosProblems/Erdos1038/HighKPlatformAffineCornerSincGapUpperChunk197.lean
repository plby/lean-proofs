import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk197
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk197
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 197. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_197 : Rat := -485802795656 / 1000000000000

theorem gapUpperCheck_197 : EvalUpper ![qOuter_197, rOuter_197]
    (sincGapE2 scalarTrigDoubles) gapUpper_197 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
