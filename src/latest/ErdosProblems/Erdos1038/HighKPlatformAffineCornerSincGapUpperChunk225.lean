import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk225
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk225
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 225. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_225 : Rat := -471686461812 / 1000000000000

theorem gapUpperCheck_225 : EvalUpper ![qOuter_225, rOuter_225]
    (sincGapE2 scalarTrigDoubles) gapUpper_225 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
