import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk228
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk228
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 228. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_228 : Rat := -470108358639 / 1000000000000

theorem gapUpperCheck_228 : EvalUpper ![qOuter_228, rOuter_228]
    (sincGapE2 scalarTrigDoubles) gapUpper_228 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
