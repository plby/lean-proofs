import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk22
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk22
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 22. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_022 : Rat := -536962439063 / 1000000000000

theorem gapUpperCheck_022 : EvalUpper ![qOuter_022, rOuter_022]
    (sincGapE2 scalarTrigDoubles) gapUpper_022 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
