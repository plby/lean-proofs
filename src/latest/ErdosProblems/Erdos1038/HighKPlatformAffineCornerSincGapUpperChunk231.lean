import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk231
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk231
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 231. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_231 : Rat := -468518158325 / 1000000000000

theorem gapUpperCheck_231 : EvalUpper ![qOuter_231, rOuter_231]
    (sincGapE2 scalarTrigDoubles) gapUpper_231 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
