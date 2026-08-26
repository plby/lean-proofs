import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk24
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk24
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 24. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_024 : Rat := -536859575804 / 1000000000000

theorem gapUpperCheck_024 : EvalUpper ![qOuter_024, rOuter_024]
    (sincGapE2 scalarTrigDoubles) gapUpper_024 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
