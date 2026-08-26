import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk28
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk28
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 28. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_028 : Rat := -536618356268 / 1000000000000

theorem gapUpperCheck_028 : EvalUpper ![qOuter_028, rOuter_028]
    (sincGapE2 scalarTrigDoubles) gapUpper_028 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
