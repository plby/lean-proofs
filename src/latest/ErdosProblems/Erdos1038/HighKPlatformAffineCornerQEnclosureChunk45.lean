import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine qOuter semantic enclosure for cell 45. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineTableData
open Erdos1038.HighKPlatformAffineSemanticCorner

def qOuter_045 : RatInterval :=
  ⟨3035481467004 / 1000000000000,
    3050799623460 / 1000000000000⟩

theorem qEnclosed_045 : EvalEnclosed
    (data ⟨45, by decide⟩).boxes
    (qmaxE scalarSqrtSteps .affine) qOuter_045 := by
  exact evalEnclosed_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
