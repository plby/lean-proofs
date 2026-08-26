import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk232
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk232
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 232. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_232 : Rat := -467985429571 / 1000000000000

theorem gapUpperCheck_232 : EvalUpper ![qOuter_232, rOuter_232]
    (sincGapE2 scalarTrigDoubles) gapUpper_232 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
