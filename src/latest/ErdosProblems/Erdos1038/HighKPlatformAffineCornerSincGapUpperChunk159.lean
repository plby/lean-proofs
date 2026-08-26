import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk159
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk159
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 159. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_159 : Rat := -502982424613 / 1000000000000

theorem gapUpperCheck_159 : EvalUpper ![qOuter_159, rOuter_159]
    (sincGapE2 scalarTrigDoubles) gapUpper_159 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
