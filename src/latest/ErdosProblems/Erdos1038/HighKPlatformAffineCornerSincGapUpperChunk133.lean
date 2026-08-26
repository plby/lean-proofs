import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk133
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk133
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 133. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_133 : Rat := -513187226301 / 1000000000000

theorem gapUpperCheck_133 : EvalUpper ![qOuter_133, rOuter_133]
    (sincGapE2 scalarTrigDoubles) gapUpper_133 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
