import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk218
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk218
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 218. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_218 : Rat := -475320804448 / 1000000000000

theorem gapUpperCheck_218 : EvalUpper ![qOuter_218, rOuter_218]
    (sincGapE2 scalarTrigDoubles) gapUpper_218 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
