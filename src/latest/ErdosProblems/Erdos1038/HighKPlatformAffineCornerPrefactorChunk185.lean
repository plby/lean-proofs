import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine prefactor semantic corner check for cell 185. -/

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

def prefactorLower_185 : Rat := -2160001 / 1000000

theorem prefactor_185 : UniformLower (data ⟨185, by decide⟩).boxes
    (prefactorE scalarLogTerms scalarSqrtSteps .affine)
    prefactorLower_185 := by
  apply uniformLower_of_evalLower
  exact evalLower_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
