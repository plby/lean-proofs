import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk13
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk13
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 13. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_013 : Rat := -537277575107 / 1000000000000

theorem gapUpperCheck_013 : EvalUpper ![qOuter_013, rOuter_013]
    (sincGapE2 scalarTrigDoubles) gapUpper_013 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
