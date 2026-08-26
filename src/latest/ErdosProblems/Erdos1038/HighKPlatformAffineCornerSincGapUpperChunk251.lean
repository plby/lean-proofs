import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk251
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk251
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 251. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_251 : Rat := -457618108475 / 1000000000000

theorem gapUpperCheck_251 : EvalUpper ![qOuter_251, rOuter_251]
    (sincGapE2 scalarTrigDoubles) gapUpper_251 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
