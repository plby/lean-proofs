import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk224
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk224
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 224. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_224 : Rat := -472209782073 / 1000000000000

theorem gapUpperCheck_224 : EvalUpper ![qOuter_224, rOuter_224]
    (sincGapE2 scalarTrigDoubles) gapUpper_224 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
