import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk32
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk32
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 32. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_032 : Rat := -536329688101 / 1000000000000

theorem gapUpperCheck_032 : EvalUpper ![qOuter_032, rOuter_032]
    (sincGapE2 scalarTrigDoubles) gapUpper_032 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
