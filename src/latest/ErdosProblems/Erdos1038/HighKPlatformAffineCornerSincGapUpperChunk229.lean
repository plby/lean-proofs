import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk229
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk229
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 229. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_229 : Rat := -469579628468 / 1000000000000

theorem gapUpperCheck_229 : EvalUpper ![qOuter_229, rOuter_229]
    (sincGapE2 scalarTrigDoubles) gapUpper_229 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
