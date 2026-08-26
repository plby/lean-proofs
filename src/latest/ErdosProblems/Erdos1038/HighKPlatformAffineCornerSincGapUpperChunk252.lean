import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk252
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk252
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 252. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_252 : Rat := -457059880951 / 1000000000000

theorem gapUpperCheck_252 : EvalUpper ![qOuter_252, rOuter_252]
    (sincGapE2 scalarTrigDoubles) gapUpper_252 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
