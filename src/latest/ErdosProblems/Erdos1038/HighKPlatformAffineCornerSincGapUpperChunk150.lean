import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk150
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk150
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 150. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_150 : Rat := -506670751092 / 1000000000000

theorem gapUpperCheck_150 : EvalUpper ![qOuter_150, rOuter_150]
    (sincGapE2 scalarTrigDoubles) gapUpper_150 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
