import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk167
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk167
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 167. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_167 : Rat := -499574591497 / 1000000000000

theorem gapUpperCheck_167 : EvalUpper ![qOuter_167, rOuter_167]
    (sincGapE2 scalarTrigDoubles) gapUpper_167 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
