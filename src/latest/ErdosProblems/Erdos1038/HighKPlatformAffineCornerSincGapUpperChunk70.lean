import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk70
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk70
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 70. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_070 : Rat := -531144174863 / 1000000000000

theorem gapUpperCheck_070 : EvalUpper ![qOuter_070, rOuter_070]
    (sincGapE2 scalarTrigDoubles) gapUpper_070 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
