import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk230
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk230
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 230. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_230 : Rat := -469049559994 / 1000000000000

theorem gapUpperCheck_230 : EvalUpper ![qOuter_230, rOuter_230]
    (sincGapE2 scalarTrigDoubles) gapUpper_230 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
