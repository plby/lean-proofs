import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk125
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk125
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk125
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 125. -/

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

def sincGapLower_125 : Rat := 265999 / 1000000

theorem sincGap_125 : UniformLower (data ⟨125, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_125 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_125) (rOuter := rOuter_125)
      (gapUpper := gapUpper_125)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_125
  · exact rEnclosed_125
  · exact gapUpperCheck_125
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
