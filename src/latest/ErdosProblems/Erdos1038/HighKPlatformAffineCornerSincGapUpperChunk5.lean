import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk5
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk5
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 5. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_005 : Rat := -537345642548 / 1000000000000

theorem gapUpperCheck_005 : EvalUpper ![qOuter_005, rOuter_005]
    (sincGapE2 scalarTrigDoubles) gapUpper_005 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
