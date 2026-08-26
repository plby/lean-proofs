import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk40
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk40
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 40. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_040 : Rat := -535608449604 / 1000000000000

theorem gapUpperCheck_040 : EvalUpper ![qOuter_040, rOuter_040]
    (sincGapE2 scalarTrigDoubles) gapUpper_040 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
