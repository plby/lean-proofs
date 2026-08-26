import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk103
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk103
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 103. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_103 : Rat := -523069809753 / 1000000000000

theorem gapUpperCheck_103 : EvalUpper ![qOuter_103, rOuter_103]
    (sincGapE2 scalarTrigDoubles) gapUpper_103 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
