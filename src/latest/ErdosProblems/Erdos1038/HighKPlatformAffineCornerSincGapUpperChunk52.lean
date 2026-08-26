import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk52
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk52
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 52. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_052 : Rat := -534159464051 / 1000000000000

theorem gapUpperCheck_052 : EvalUpper ![qOuter_052, rOuter_052]
    (sincGapE2 scalarTrigDoubles) gapUpper_052 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
