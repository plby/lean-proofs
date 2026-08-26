import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk47
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk47
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 47. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_047 : Rat := -534817372746 / 1000000000000

theorem gapUpperCheck_047 : EvalUpper ![qOuter_047, rOuter_047]
    (sincGapE2 scalarTrigDoubles) gapUpper_047 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
