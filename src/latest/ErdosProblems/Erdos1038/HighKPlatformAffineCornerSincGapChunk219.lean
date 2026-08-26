import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk219
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk219
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk219
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 219. -/

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

def sincGapLower_219 : Rat := 224999 / 1000000

theorem sincGap_219 : UniformLower (data ⟨219, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_219 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_219) (rOuter := rOuter_219)
      (gapUpper := gapUpper_219)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_219
  · exact rEnclosed_219
  · exact gapUpperCheck_219
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
