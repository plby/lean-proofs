import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk195
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk195
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 195. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_195 : Rat := -486766602931 / 1000000000000

theorem gapUpperCheck_195 : EvalUpper ![qOuter_195, rOuter_195]
    (sincGapE2 scalarTrigDoubles) gapUpper_195 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
