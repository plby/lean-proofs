import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk122
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk122
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 122. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_122 : Rat := -517064762048 / 1000000000000

theorem gapUpperCheck_122 : EvalUpper ![qOuter_122, rOuter_122]
    (sincGapE2 scalarTrigDoubles) gapUpper_122 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
