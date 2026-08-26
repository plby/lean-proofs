import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk242
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk242
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 242. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_242 : Rat := -462586260673 / 1000000000000

theorem gapUpperCheck_242 : EvalUpper ![qOuter_242, rOuter_242]
    (sincGapE2 scalarTrigDoubles) gapUpper_242 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
