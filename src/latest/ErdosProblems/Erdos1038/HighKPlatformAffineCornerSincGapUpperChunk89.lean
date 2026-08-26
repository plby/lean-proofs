import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk89
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk89
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 89. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_089 : Rat := -526881379822 / 1000000000000

theorem gapUpperCheck_089 : EvalUpper ![qOuter_089, rOuter_089]
    (sincGapE2 scalarTrigDoubles) gapUpper_089 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
