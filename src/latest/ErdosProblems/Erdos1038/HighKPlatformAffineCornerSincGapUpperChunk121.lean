import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk121
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk121
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 121. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_121 : Rat := -517403231416 / 1000000000000

theorem gapUpperCheck_121 : EvalUpper ![qOuter_121, rOuter_121]
    (sincGapE2 scalarTrigDoubles) gapUpper_121 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
