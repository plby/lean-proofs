import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk81
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk81
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 81. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_081 : Rat := -528808027901 / 1000000000000

theorem gapUpperCheck_081 : EvalUpper ![qOuter_081, rOuter_081]
    (sincGapE2 scalarTrigDoubles) gapUpper_081 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
