import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk27
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk27
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 27. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_027 : Rat := -536683100148 / 1000000000000

theorem gapUpperCheck_027 : EvalUpper ![qOuter_027, rOuter_027]
    (sincGapE2 scalarTrigDoubles) gapUpper_027 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
