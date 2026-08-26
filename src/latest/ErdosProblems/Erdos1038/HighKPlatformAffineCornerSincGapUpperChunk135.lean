import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk135
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk135
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 135. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_135 : Rat := -512452698855 / 1000000000000

theorem gapUpperCheck_135 : EvalUpper ![qOuter_135, rOuter_135]
    (sincGapE2 scalarTrigDoubles) gapUpper_135 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
