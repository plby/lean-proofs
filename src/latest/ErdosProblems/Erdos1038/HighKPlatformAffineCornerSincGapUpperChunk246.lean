import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk246
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk246
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 246. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_246 : Rat := -460390705434 / 1000000000000

theorem gapUpperCheck_246 : EvalUpper ![qOuter_246, rOuter_246]
    (sincGapE2 scalarTrigDoubles) gapUpper_246 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
