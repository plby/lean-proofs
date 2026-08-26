import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk86
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk86
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 86. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_086 : Rat := -527625877643 / 1000000000000

theorem gapUpperCheck_086 : EvalUpper ![qOuter_086, rOuter_086]
    (sincGapE2 scalarTrigDoubles) gapUpper_086 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
