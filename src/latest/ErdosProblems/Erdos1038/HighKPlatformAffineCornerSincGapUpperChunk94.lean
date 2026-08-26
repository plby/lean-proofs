import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk94
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk94
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 94. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_094 : Rat := -525583015552 / 1000000000000

theorem gapUpperCheck_094 : EvalUpper ![qOuter_094, rOuter_094]
    (sincGapE2 scalarTrigDoubles) gapUpper_094 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
