import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk238
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk238
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 238. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_238 : Rat := -464761467026 / 1000000000000

theorem gapUpperCheck_238 : EvalUpper ![qOuter_238, rOuter_238]
    (sincGapE2 scalarTrigDoubles) gapUpper_238 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
