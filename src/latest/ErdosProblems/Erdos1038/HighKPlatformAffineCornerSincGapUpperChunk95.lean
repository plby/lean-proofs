import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk95
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk95
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 95. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_095 : Rat := -525314837410 / 1000000000000

theorem gapUpperCheck_095 : EvalUpper ![qOuter_095, rOuter_095]
    (sincGapE2 scalarTrigDoubles) gapUpper_095 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
