import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk191
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk191
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 191. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_191 : Rat := -488675439348 / 1000000000000

theorem gapUpperCheck_191 : EvalUpper ![qOuter_191, rOuter_191]
    (sincGapE2 scalarTrigDoubles) gapUpper_191 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
