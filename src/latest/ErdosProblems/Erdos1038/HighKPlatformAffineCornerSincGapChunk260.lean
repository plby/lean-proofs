import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk260
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk260
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk260
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 260. -/

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

def sincGapLower_260 : Rat := 203999 / 1000000

theorem sincGap_260 : UniformLower (data ⟨260, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_260 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_260) (rOuter := rOuter_260)
      (gapUpper := gapUpper_260)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_260
  · exact rEnclosed_260
  · exact gapUpperCheck_260
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
