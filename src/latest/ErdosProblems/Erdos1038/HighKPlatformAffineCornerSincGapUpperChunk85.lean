import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk85
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk85
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 85. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_085 : Rat := -527868209739 / 1000000000000

theorem gapUpperCheck_085 : EvalUpper ![qOuter_085, rOuter_085]
    (sincGapE2 scalarTrigDoubles) gapUpper_085 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
