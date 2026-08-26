import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk53
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk53
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 53. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_053 : Rat := -534018528854 / 1000000000000

theorem gapUpperCheck_053 : EvalUpper ![qOuter_053, rOuter_053]
    (sincGapE2 scalarTrigDoubles) gapUpper_053 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
