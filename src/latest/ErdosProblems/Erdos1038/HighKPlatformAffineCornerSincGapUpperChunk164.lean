import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk164
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk164
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 164. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_164 : Rat := -500866402610 / 1000000000000

theorem gapUpperCheck_164 : EvalUpper ![qOuter_164, rOuter_164]
    (sincGapE2 scalarTrigDoubles) gapUpper_164 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
