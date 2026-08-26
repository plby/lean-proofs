import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk237
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk237
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 237. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_237 : Rat := -465302052359 / 1000000000000

theorem gapUpperCheck_237 : EvalUpper ![qOuter_237, rOuter_237]
    (sincGapE2 scalarTrigDoubles) gapUpper_237 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
