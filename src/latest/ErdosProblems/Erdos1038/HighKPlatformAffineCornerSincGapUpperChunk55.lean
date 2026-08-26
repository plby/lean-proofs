import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk55
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk55
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 55. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_055 : Rat := -533727277841 / 1000000000000

theorem gapUpperCheck_055 : EvalUpper ![qOuter_055, rOuter_055]
    (sincGapE2 scalarTrigDoubles) gapUpper_055 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
