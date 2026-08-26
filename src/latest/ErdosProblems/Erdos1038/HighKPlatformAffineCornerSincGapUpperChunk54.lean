import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk54
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk54
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 54. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_054 : Rat := -533874467573 / 1000000000000

theorem gapUpperCheck_054 : EvalUpper ![qOuter_054, rOuter_054]
    (sincGapE2 scalarTrigDoubles) gapUpper_054 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
