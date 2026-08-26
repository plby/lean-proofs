import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk38
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk38
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 38. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_038 : Rat := -535806900601 / 1000000000000

theorem gapUpperCheck_038 : EvalUpper ![qOuter_038, rOuter_038]
    (sincGapE2 scalarTrigDoubles) gapUpper_038 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
