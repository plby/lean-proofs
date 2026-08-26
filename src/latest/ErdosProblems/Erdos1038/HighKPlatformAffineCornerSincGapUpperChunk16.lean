import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk16
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk16
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 16. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_016 : Rat := -537199682781 / 1000000000000

theorem gapUpperCheck_016 : EvalUpper ![qOuter_016, rOuter_016]
    (sincGapE2 scalarTrigDoubles) gapUpper_016 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
