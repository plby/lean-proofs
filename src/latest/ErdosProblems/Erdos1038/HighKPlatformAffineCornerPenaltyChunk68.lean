import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine penalty semantic corner check for cell 68. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineTableData
open Erdos1038.HighKPlatformAffineCornerComponents
open Erdos1038.HighKPlatformAffineSemanticCorner

def penaltyLower_068 : Rat := 2109999 / 1000000

theorem penalty_068 : UniformLower (data ⟨68, by decide⟩).boxes
    (penaltyQuotientE scalarLogTerms scalarSqrtSteps .affine)
    penaltyLower_068 := by
  apply uniformLower_penaltyQuotient_of_negCeff
  · exact evalPositive_of_check (by kernel_decide)
  · exact evalPositive_of_check (by kernel_decide)
  · exact evalLower_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
