import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk120
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk120
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 120. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_120 : Rat := -517739297468 / 1000000000000

theorem gapUpperCheck_120 : EvalUpper ![qOuter_120, rOuter_120]
    (sincGapE2 scalarTrigDoubles) gapUpper_120 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
