import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk87
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk87
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 87. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_087 : Rat := -527380620600 / 1000000000000

theorem gapUpperCheck_087 : EvalUpper ![qOuter_087, rOuter_087]
    (sincGapE2 scalarTrigDoubles) gapUpper_087 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
