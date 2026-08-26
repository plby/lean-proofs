import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk19
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk19
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk19
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 19. -/

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

def sincGapLower_019 : Rat := 287999 / 1000000

theorem sincGap_019 : UniformLower (data ⟨19, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_019 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_019) (rOuter := rOuter_019)
      (gapUpper := gapUpper_019)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_019
  · exact rEnclosed_019
  · exact gapUpperCheck_019
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
