import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk168
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk168
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 168. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_168 : Rat := -499140351874 / 1000000000000

theorem gapUpperCheck_168 : EvalUpper ![qOuter_168, rOuter_168]
    (sincGapE2 scalarTrigDoubles) gapUpper_168 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
