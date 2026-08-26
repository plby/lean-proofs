import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk39
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk39
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 39. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_039 : Rat := -535709196480 / 1000000000000

theorem gapUpperCheck_039 : EvalUpper ![qOuter_039, rOuter_039]
    (sincGapE2 scalarTrigDoubles) gapUpper_039 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
