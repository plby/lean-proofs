import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine qOuter semantic enclosure for cell 133. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineTableData
open Erdos1038.HighKPlatformAffineSemanticCorner

def qOuter_133 : RatInterval :=
  ⟨2950878268587 / 1000000000000,
    2965363418781 / 1000000000000⟩

theorem qEnclosed_133 : EvalEnclosed
    (data ⟨133, by decide⟩).boxes
    (qmaxE scalarSqrtSteps .affine) qOuter_133 := by
  exact evalEnclosed_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
