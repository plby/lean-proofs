import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk180
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk180
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 180. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_180 : Rat := -493791872711 / 1000000000000

theorem gapUpperCheck_180 : EvalUpper ![qOuter_180, rOuter_180]
    (sincGapE2 scalarTrigDoubles) gapUpper_180 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
