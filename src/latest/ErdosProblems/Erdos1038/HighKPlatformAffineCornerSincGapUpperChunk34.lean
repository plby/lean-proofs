import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk34
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk34
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 34. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_034 : Rat := -536167455368 / 1000000000000

theorem gapUpperCheck_034 : EvalUpper ![qOuter_034, rOuter_034]
    (sincGapE2 scalarTrigDoubles) gapUpper_034 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
