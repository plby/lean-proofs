import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk92
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk92
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 92. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_092 : Rat := -526110908733 / 1000000000000

theorem gapUpperCheck_092 : EvalUpper ![qOuter_092, rOuter_092]
    (sincGapE2 scalarTrigDoubles) gapUpper_092 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
