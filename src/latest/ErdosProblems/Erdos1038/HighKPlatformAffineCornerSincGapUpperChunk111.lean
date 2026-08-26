import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk111
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk111
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 111. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_111 : Rat := -520653210488 / 1000000000000

theorem gapUpperCheck_111 : EvalUpper ![qOuter_111, rOuter_111]
    (sincGapE2 scalarTrigDoubles) gapUpper_111 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
