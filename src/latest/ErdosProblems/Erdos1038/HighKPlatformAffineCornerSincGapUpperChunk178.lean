import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk178
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk178
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 178. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_178 : Rat := -494700571124 / 1000000000000

theorem gapUpperCheck_178 : EvalUpper ![qOuter_178, rOuter_178]
    (sincGapE2 scalarTrigDoubles) gapUpper_178 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
