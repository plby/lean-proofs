import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk14
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk14
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 14. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_014 : Rat := -537254679394 / 1000000000000

theorem gapUpperCheck_014 : EvalUpper ![qOuter_014, rOuter_014]
    (sincGapE2 scalarTrigDoubles) gapUpper_014 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
