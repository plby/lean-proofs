import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk186
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk186
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 186. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_186 : Rat := -491025622536 / 1000000000000

theorem gapUpperCheck_186 : EvalUpper ![qOuter_186, rOuter_186]
    (sincGapE2 scalarTrigDoubles) gapUpper_186 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
