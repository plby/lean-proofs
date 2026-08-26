import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk198
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk198
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 198. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_198 : Rat := -485318571513 / 1000000000000

theorem gapUpperCheck_198 : EvalUpper ![qOuter_198, rOuter_198]
    (sincGapE2 scalarTrigDoubles) gapUpper_198 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
