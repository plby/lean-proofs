import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk26
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk26
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 26. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_026 : Rat := -536744882961 / 1000000000000

theorem gapUpperCheck_026 : EvalUpper ![qOuter_026, rOuter_026]
    (sincGapE2 scalarTrigDoubles) gapUpper_026 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
