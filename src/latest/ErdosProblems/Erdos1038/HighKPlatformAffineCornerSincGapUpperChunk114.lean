import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk114
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk114
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 114. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_114 : Rat := -519704364535 / 1000000000000

theorem gapUpperCheck_114 : EvalUpper ![qOuter_114, rOuter_114]
    (sincGapE2 scalarTrigDoubles) gapUpper_114 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
