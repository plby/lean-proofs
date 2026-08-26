import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk9
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk9
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 9. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_009 : Rat := -537337763849 / 1000000000000

theorem gapUpperCheck_009 : EvalUpper ![qOuter_009, rOuter_009]
    (sincGapE2 scalarTrigDoubles) gapUpper_009 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
