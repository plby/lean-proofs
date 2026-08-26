import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk199
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk199
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 199. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_199 : Rat := -484832810868 / 1000000000000

theorem gapUpperCheck_199 : EvalUpper ![qOuter_199, rOuter_199]
    (sincGapE2 scalarTrigDoubles) gapUpper_199 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
