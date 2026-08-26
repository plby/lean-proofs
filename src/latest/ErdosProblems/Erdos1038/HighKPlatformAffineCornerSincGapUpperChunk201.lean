import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk201
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk201
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 201. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_201 : Rat := -483856709151 / 1000000000000

theorem gapUpperCheck_201 : EvalUpper ![qOuter_201, rOuter_201]
    (sincGapE2 scalarTrigDoubles) gapUpper_201 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
