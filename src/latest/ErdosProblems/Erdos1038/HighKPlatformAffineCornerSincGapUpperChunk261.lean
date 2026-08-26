import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk261
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk261
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 261. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_261 : Rat := -451981210031 / 1000000000000

theorem gapUpperCheck_261 : EvalUpper ![qOuter_261, rOuter_261]
    (sincGapE2 scalarTrigDoubles) gapUpper_261 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
