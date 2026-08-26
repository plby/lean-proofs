import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk59
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk59
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 59. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_059 : Rat := -533107207536 / 1000000000000

theorem gapUpperCheck_059 : EvalUpper ![qOuter_059, rOuter_059]
    (sincGapE2 scalarTrigDoubles) gapUpper_059 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
