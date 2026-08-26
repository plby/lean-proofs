import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk88
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk88
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk88
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 88. -/

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

def sincGapLower_088 : Rat := 276999 / 1000000

theorem sincGap_088 : UniformLower (data ⟨88, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_088 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_088) (rOuter := rOuter_088)
      (gapUpper := gapUpper_088)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_088
  · exact rEnclosed_088
  · exact gapUpperCheck_088
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
