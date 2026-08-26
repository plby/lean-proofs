import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk63
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk63
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 63. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_063 : Rat := -532437042222 / 1000000000000

theorem gapUpperCheck_063 : EvalUpper ![qOuter_063, rOuter_063]
    (sincGapE2 scalarTrigDoubles) gapUpper_063 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
