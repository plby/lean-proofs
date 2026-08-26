import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk257
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk257
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 257. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_257 : Rat := -454250449716 / 1000000000000

theorem gapUpperCheck_257 : EvalUpper ![qOuter_257, rOuter_257]
    (sincGapE2 scalarTrigDoubles) gapUpper_257 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
