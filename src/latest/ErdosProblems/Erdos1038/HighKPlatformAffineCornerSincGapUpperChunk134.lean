import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk134
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk134
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 134. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_134 : Rat := -512821069388 / 1000000000000

theorem gapUpperCheck_134 : EvalUpper ![qOuter_134, rOuter_134]
    (sincGapE2 scalarTrigDoubles) gapUpper_134 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
