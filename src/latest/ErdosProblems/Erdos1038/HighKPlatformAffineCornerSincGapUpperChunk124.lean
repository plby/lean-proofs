import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk124
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk124
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 124. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_124 : Rat := -516380672586 / 1000000000000

theorem gapUpperCheck_124 : EvalUpper ![qOuter_124, rOuter_124]
    (sincGapE2 scalarTrigDoubles) gapUpper_124 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
