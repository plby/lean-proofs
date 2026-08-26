import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk108
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk108
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 108. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_108 : Rat := -521579041543 / 1000000000000

theorem gapUpperCheck_108 : EvalUpper ![qOuter_108, rOuter_108]
    (sincGapE2 scalarTrigDoubles) gapUpper_108 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
