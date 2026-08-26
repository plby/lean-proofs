import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk115
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk115
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 115. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_115 : Rat := -519383040094 / 1000000000000

theorem gapUpperCheck_115 : EvalUpper ![qOuter_115, rOuter_115]
    (sincGapE2 scalarTrigDoubles) gapUpper_115 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
