import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk6
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk6
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 6. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_006 : Rat := -537348764835 / 1000000000000

theorem gapUpperCheck_006 : EvalUpper ![qOuter_006, rOuter_006]
    (sincGapE2 scalarTrigDoubles) gapUpper_006 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
