import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk12
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk12
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 12. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_012 : Rat := -537297366741 / 1000000000000

theorem gapUpperCheck_012 : EvalUpper ![qOuter_012, rOuter_012]
    (sincGapE2 scalarTrigDoubles) gapUpper_012 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
