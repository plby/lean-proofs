import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk162
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk162
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 162. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_162 : Rat := -501718414694 / 1000000000000

theorem gapUpperCheck_162 : EvalUpper ![qOuter_162, rOuter_162]
    (sincGapE2 scalarTrigDoubles) gapUpper_162 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
