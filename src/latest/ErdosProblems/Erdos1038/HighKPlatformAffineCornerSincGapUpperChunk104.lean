import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk104
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk104
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 104. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_104 : Rat := -522776956834 / 1000000000000

theorem gapUpperCheck_104 : EvalUpper ![qOuter_104, rOuter_104]
    (sincGapE2 scalarTrigDoubles) gapUpper_104 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
