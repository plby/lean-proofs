import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk37
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk37
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 37. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_037 : Rat := -535901570590 / 1000000000000

theorem gapUpperCheck_037 : EvalUpper ![qOuter_037, rOuter_037]
    (sincGapE2 scalarTrigDoubles) gapUpper_037 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
