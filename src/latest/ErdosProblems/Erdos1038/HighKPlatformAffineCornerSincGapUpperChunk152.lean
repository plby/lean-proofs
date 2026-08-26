import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk152
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk152
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 152. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_152 : Rat := -505864837067 / 1000000000000

theorem gapUpperCheck_152 : EvalUpper ![qOuter_152, rOuter_152]
    (sincGapE2 scalarTrigDoubles) gapUpper_152 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
