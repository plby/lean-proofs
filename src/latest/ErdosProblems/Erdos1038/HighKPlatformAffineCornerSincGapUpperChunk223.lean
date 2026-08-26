import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk223
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk223
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 223. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_223 : Rat := -472731735813 / 1000000000000

theorem gapUpperCheck_223 : EvalUpper ![qOuter_223, rOuter_223]
    (sincGapE2 scalarTrigDoubles) gapUpper_223 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
