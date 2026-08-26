import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk19
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk19
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 19. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_019 : Rat := -537094499712 / 1000000000000

theorem gapUpperCheck_019 : EvalUpper ![qOuter_019, rOuter_019]
    (sincGapE2 scalarTrigDoubles) gapUpper_019 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
