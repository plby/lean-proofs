import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk243
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk243
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 243. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_243 : Rat := -462039267298 / 1000000000000

theorem gapUpperCheck_243 : EvalUpper ![qOuter_243, rOuter_243]
    (sincGapE2 scalarTrigDoubles) gapUpper_243 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
