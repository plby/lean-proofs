import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk210
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk210
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 210. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_210 : Rat := -479390086491 / 1000000000000

theorem gapUpperCheck_210 : EvalUpper ![qOuter_210, rOuter_210]
    (sincGapE2 scalarTrigDoubles) gapUpper_210 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
