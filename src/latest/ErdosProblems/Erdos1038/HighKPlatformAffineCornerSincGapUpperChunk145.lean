import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk145
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk145
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 145. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_145 : Rat := -508650264642 / 1000000000000

theorem gapUpperCheck_145 : EvalUpper ![qOuter_145, rOuter_145]
    (sincGapE2 scalarTrigDoubles) gapUpper_145 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
