import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk123
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk123
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 123. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_123 : Rat := -516723903983 / 1000000000000

theorem gapUpperCheck_123 : EvalUpper ![qOuter_123, rOuter_123]
    (sincGapE2 scalarTrigDoubles) gapUpper_123 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
