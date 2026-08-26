import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk149
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk149
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 149. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_149 : Rat := -507070709569 / 1000000000000

theorem gapUpperCheck_149 : EvalUpper ![qOuter_149, rOuter_149]
    (sincGapE2 scalarTrigDoubles) gapUpper_149 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
