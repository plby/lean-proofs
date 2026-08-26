import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk49
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk49
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 49. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_049 : Rat := -534563546108 / 1000000000000

theorem gapUpperCheck_049 : EvalUpper ![qOuter_049, rOuter_049]
    (sincGapE2 scalarTrigDoubles) gapUpper_049 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
