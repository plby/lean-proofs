import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk42
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk42
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 42. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_042 : Rat := -535397795473 / 1000000000000

theorem gapUpperCheck_042 : EvalUpper ![qOuter_042, rOuter_042]
    (sincGapE2 scalarTrigDoubles) gapUpper_042 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
