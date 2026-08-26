import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk31
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk31
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 31. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_031 : Rat := -536406319592 / 1000000000000

theorem gapUpperCheck_031 : EvalUpper ![qOuter_031, rOuter_031]
    (sincGapE2 scalarTrigDoubles) gapUpper_031 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
