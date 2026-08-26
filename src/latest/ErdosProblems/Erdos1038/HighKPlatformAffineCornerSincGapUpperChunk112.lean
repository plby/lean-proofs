import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk112
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk112
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 112. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_112 : Rat := -520339464717 / 1000000000000

theorem gapUpperCheck_112 : EvalUpper ![qOuter_112, rOuter_112]
    (sincGapE2 scalarTrigDoubles) gapUpper_112 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
