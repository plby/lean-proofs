import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk249
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk249
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 249. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_249 : Rat := -458730868987 / 1000000000000

theorem gapUpperCheck_249 : EvalUpper ![qOuter_249, rOuter_249]
    (sincGapE2 scalarTrigDoubles) gapUpper_249 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
