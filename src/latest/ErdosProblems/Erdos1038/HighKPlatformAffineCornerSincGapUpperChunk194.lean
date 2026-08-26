import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk194
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk194
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 194. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_194 : Rat := -487246170632 / 1000000000000

theorem gapUpperCheck_194 : EvalUpper ![qOuter_194, rOuter_194]
    (sincGapE2 scalarTrigDoubles) gapUpper_194 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
