import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk109
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk109
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk109
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 109. -/

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

def sincGapLower_109 : Rat := 270999 / 1000000

theorem sincGap_109 : UniformLower (data ⟨109, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_109 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_109) (rOuter := rOuter_109)
      (gapUpper := gapUpper_109)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_109
  · exact rEnclosed_109
  · exact gapUpperCheck_109
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
