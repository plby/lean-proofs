import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk182
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk182
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk182
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 182. -/

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

def sincGapLower_182 : Rat := 241999 / 1000000

theorem sincGap_182 : UniformLower (data ⟨182, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_182 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_182) (rOuter := rOuter_182)
      (gapUpper := gapUpper_182)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_182
  · exact rEnclosed_182
  · exact gapUpperCheck_182
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
