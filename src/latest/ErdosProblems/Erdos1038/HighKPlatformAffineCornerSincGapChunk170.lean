import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk170
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk170
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk170
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 170. -/

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

def sincGapLower_170 : Rat := 247999 / 1000000

theorem sincGap_170 : UniformLower (data ⟨170, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_170 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_170) (rOuter := rOuter_170)
      (gapUpper := gapUpper_170)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_170
  · exact rEnclosed_170
  · exact gapUpperCheck_170
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
