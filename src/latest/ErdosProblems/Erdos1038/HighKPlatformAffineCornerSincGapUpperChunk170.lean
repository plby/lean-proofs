import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk170
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk170
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 170. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_170 : Rat := -498266481294 / 1000000000000

theorem gapUpperCheck_170 : EvalUpper ![qOuter_170, rOuter_170]
    (sincGapE2 scalarTrigDoubles) gapUpper_170 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
