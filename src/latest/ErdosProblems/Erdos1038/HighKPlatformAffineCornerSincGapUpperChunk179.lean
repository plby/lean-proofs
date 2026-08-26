import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk179
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk179
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 179. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_179 : Rat := -494247069080 / 1000000000000

theorem gapUpperCheck_179 : EvalUpper ![qOuter_179, rOuter_179]
    (sincGapE2 scalarTrigDoubles) gapUpper_179 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
