import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk100
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk100
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 100. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_100 : Rat := -523932221514 / 1000000000000

theorem gapUpperCheck_100 : EvalUpper ![qOuter_100, rOuter_100]
    (sincGapE2 scalarTrigDoubles) gapUpper_100 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
