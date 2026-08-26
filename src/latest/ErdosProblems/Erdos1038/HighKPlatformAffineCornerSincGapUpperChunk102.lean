import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk102
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk102
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 102. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_102 : Rat := -523359982148 / 1000000000000

theorem gapUpperCheck_102 : EvalUpper ![qOuter_102, rOuter_102]
    (sincGapE2 scalarTrigDoubles) gapUpper_102 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
