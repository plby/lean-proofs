import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk190
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk190
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 190. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_190 : Rat := -489148690872 / 1000000000000

theorem gapUpperCheck_190 : EvalUpper ![qOuter_190, rOuter_190]
    (sincGapE2 scalarTrigDoubles) gapUpper_190 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
