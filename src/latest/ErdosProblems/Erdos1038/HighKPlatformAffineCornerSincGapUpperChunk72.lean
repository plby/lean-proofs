import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk72
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk72
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 72. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_072 : Rat := -530746899727 / 1000000000000

theorem gapUpperCheck_072 : EvalUpper ![qOuter_072, rOuter_072]
    (sincGapE2 scalarTrigDoubles) gapUpper_072 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
