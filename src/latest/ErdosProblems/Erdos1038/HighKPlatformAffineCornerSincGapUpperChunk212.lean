import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk212
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk212
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 212. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_212 : Rat := -478381352690 / 1000000000000

theorem gapUpperCheck_212 : EvalUpper ![qOuter_212, rOuter_212]
    (sincGapE2 scalarTrigDoubles) gapUpper_212 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
