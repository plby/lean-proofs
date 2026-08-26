import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk82
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk82
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 82. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_082 : Rat := -528577523985 / 1000000000000

theorem gapUpperCheck_082 : EvalUpper ![qOuter_082, rOuter_082]
    (sincGapE2 scalarTrigDoubles) gapUpper_082 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
