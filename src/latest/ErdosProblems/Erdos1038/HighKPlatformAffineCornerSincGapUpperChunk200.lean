import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk200
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk200
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 200. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_200 : Rat := -484345520894 / 1000000000000

theorem gapUpperCheck_200 : EvalUpper ![qOuter_200, rOuter_200]
    (sincGapE2 scalarTrigDoubles) gapUpper_200 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
