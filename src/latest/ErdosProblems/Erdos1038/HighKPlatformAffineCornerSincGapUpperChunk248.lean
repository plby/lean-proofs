import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk248
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk248
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 248. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_248 : Rat := -459285392692 / 1000000000000

theorem gapUpperCheck_248 : EvalUpper ![qOuter_248, rOuter_248]
    (sincGapE2 scalarTrigDoubles) gapUpper_248 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
