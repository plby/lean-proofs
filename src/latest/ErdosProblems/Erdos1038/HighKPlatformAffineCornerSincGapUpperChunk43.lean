import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk43
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk43
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 43. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_043 : Rat := -535287873114 / 1000000000000

theorem gapUpperCheck_043 : EvalUpper ![qOuter_043, rOuter_043]
    (sincGapE2 scalarTrigDoubles) gapUpper_043 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
