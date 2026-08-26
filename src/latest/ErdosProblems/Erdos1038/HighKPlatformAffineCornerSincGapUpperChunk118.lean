import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk118
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk118
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 118. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_118 : Rat := -518404157359 / 1000000000000

theorem gapUpperCheck_118 : EvalUpper ![qOuter_118, rOuter_118]
    (sincGapE2 scalarTrigDoubles) gapUpper_118 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
