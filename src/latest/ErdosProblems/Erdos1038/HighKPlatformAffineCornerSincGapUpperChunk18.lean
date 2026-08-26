import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk18
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk18
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 18. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_018 : Rat := -537132562977 / 1000000000000

theorem gapUpperCheck_018 : EvalUpper ![qOuter_018, rOuter_018]
    (sincGapE2 scalarTrigDoubles) gapUpper_018 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
