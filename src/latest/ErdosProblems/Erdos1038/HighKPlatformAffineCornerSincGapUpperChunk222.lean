import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk222
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk222
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 222. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_222 : Rat := -473252317417 / 1000000000000

theorem gapUpperCheck_222 : EvalUpper ![qOuter_222, rOuter_222]
    (sincGapE2 scalarTrigDoubles) gapUpper_222 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
