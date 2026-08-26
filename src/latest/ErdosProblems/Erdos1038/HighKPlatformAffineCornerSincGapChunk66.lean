import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk66
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk66
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk66
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 66. -/

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

def sincGapLower_066 : Rat := 281999 / 1000000

theorem sincGap_066 : UniformLower (data ⟨66, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_066 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_066) (rOuter := rOuter_066)
      (gapUpper := gapUpper_066)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_066
  · exact rEnclosed_066
  · exact gapUpperCheck_066
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
