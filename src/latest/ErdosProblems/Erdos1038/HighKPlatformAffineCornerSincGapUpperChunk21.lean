import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk21
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk21
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 21. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_021 : Rat := -537009429437 / 1000000000000

theorem gapUpperCheck_021 : EvalUpper ![qOuter_021, rOuter_021]
    (sincGapE2 scalarTrigDoubles) gapUpper_021 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
