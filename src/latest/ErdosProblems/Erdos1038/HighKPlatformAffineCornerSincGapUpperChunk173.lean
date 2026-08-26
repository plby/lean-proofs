import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk173
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk173
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 173. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_173 : Rat := -496942347526 / 1000000000000

theorem gapUpperCheck_173 : EvalUpper ![qOuter_173, rOuter_173]
    (sincGapE2 scalarTrigDoubles) gapUpper_173 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
