import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk205
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk205
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 205. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_205 : Rat := -481886385469 / 1000000000000

theorem gapUpperCheck_205 : EvalUpper ![qOuter_205, rOuter_205]
    (sincGapE2 scalarTrigDoubles) gapUpper_205 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
