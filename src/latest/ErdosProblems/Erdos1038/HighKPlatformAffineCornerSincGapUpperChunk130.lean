import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk130
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk130
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 130. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_130 : Rat := -514272274731 / 1000000000000

theorem gapUpperCheck_130 : EvalUpper ![qOuter_130, rOuter_130]
    (sincGapE2 scalarTrigDoubles) gapUpper_130 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
