import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk46
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk46
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk46
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 46. -/

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

def sincGapLower_046 : Rat := 285999 / 1000000

theorem sincGap_046 : UniformLower (data ⟨46, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_046 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_046) (rOuter := rOuter_046)
      (gapUpper := gapUpper_046)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_046
  · exact rEnclosed_046
  · exact gapUpperCheck_046
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
