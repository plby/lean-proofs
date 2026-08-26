import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk142
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk142
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 142. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_142 : Rat := -509813283699 / 1000000000000

theorem gapUpperCheck_142 : EvalUpper ![qOuter_142, rOuter_142]
    (sincGapE2 scalarTrigDoubles) gapUpper_142 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
