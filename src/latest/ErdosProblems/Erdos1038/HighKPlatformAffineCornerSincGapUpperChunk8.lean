import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk8
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk8
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 8. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_008 : Rat := -537344764580 / 1000000000000

theorem gapUpperCheck_008 : EvalUpper ![qOuter_008, rOuter_008]
    (sincGapE2 scalarTrigDoubles) gapUpper_008 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
