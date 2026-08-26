import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk122
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk122
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk122
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 122. -/

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

def sincGapLower_122 : Rat := 266999 / 1000000

theorem sincGap_122 : UniformLower (data ⟨122, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_122 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_122) (rOuter := rOuter_122)
      (gapUpper := gapUpper_122)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_122
  · exact rEnclosed_122
  · exact gapUpperCheck_122
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
