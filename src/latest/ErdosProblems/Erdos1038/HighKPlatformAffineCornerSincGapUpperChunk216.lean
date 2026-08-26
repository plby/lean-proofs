import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk216
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk216
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 216. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_216 : Rat := -476346660270 / 1000000000000

theorem gapUpperCheck_216 : EvalUpper ![qOuter_216, rOuter_216]
    (sincGapE2 scalarTrigDoubles) gapUpper_216 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
