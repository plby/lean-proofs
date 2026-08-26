import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk138
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk138
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 138. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_138 : Rat := -511334444603 / 1000000000000

theorem gapUpperCheck_138 : EvalUpper ![qOuter_138, rOuter_138]
    (sincGapE2 scalarTrigDoubles) gapUpper_138 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
