import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk234
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk234
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk234
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 234. -/

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

def sincGapLower_234 : Rat := 217999 / 1000000

theorem sincGap_234 : UniformLower (data ⟨234, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_234 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_234) (rOuter := rOuter_234)
      (gapUpper := gapUpper_234)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_234
  · exact rEnclosed_234
  · exact gapUpperCheck_234
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
