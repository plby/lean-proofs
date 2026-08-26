import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk3
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk3
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 3. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_003 : Rat := -537328802374 / 1000000000000

theorem gapUpperCheck_003 : EvalUpper ![qOuter_003, rOuter_003]
    (sincGapE2 scalarTrigDoubles) gapUpper_003 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
