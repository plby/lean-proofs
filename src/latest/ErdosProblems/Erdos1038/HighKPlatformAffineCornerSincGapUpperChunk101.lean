import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk101
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk101
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 101. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_101 : Rat := -523647457482 / 1000000000000

theorem gapUpperCheck_101 : EvalUpper ![qOuter_101, rOuter_101]
    (sincGapE2 scalarTrigDoubles) gapUpper_101 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
