import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk187
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk187
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 187. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_187 : Rat := -490558817383 / 1000000000000

theorem gapUpperCheck_187 : EvalUpper ![qOuter_187, rOuter_187]
    (sincGapE2 scalarTrigDoubles) gapUpper_187 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
