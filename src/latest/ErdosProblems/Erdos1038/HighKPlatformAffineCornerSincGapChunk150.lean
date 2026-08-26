import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk150
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk150
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk150
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 150. -/

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

def sincGapLower_150 : Rat := 255999 / 1000000

theorem sincGap_150 : UniformLower (data ⟨150, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_150 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_150) (rOuter := rOuter_150)
      (gapUpper := gapUpper_150)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_150
  · exact rEnclosed_150
  · exact gapUpperCheck_150
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
