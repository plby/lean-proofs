import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk207
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk207
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 207. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_207 : Rat := -480892277408 / 1000000000000

theorem gapUpperCheck_207 : EvalUpper ![qOuter_207, rOuter_207]
    (sincGapE2 scalarTrigDoubles) gapUpper_207 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
