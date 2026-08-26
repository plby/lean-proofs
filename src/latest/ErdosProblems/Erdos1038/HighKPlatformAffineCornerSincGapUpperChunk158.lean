import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk158
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk158
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 158. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_158 : Rat := -503399981593 / 1000000000000

theorem gapUpperCheck_158 : EvalUpper ![qOuter_158, rOuter_158]
    (sincGapE2 scalarTrigDoubles) gapUpper_158 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
