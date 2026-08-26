import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk97
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk97
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 97. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_097 : Rat := -524770091776 / 1000000000000

theorem gapUpperCheck_097 : EvalUpper ![qOuter_097, rOuter_097]
    (sincGapE2 scalarTrigDoubles) gapUpper_097 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
