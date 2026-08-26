import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk166
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk166
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk166
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 166. -/

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

def sincGapLower_166 : Rat := 249999 / 1000000

theorem sincGap_166 : UniformLower (data ⟨166, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_166 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_166) (rOuter := rOuter_166)
      (gapUpper := gapUpper_166)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_166
  · exact rEnclosed_166
  · exact gapUpperCheck_166
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
