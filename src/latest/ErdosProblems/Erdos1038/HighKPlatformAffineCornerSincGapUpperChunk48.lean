import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk48
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk48
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 48. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_048 : Rat := -534692012438 / 1000000000000

theorem gapUpperCheck_048 : EvalUpper ![qOuter_048, rOuter_048]
    (sincGapE2 scalarTrigDoubles) gapUpper_048 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
