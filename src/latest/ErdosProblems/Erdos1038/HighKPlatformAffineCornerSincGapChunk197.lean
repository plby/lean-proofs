import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk197
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk197
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk197
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 197. -/

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

def sincGapLower_197 : Rat := 235999 / 1000000

theorem sincGap_197 : UniformLower (data ⟨197, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_197 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_197) (rOuter := rOuter_197)
      (gapUpper := gapUpper_197)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_197
  · exact rEnclosed_197
  · exact gapUpperCheck_197
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
