import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk219
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk219
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 219. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_219 : Rat := -474805770170 / 1000000000000

theorem gapUpperCheck_219 : EvalUpper ![qOuter_219, rOuter_219]
    (sincGapE2 scalarTrigDoubles) gapUpper_219 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
