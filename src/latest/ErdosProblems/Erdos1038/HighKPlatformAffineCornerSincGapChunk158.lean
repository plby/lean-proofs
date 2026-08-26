import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk158
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk158
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk158
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 158. -/

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

def sincGapLower_158 : Rat := 252999 / 1000000

theorem sincGap_158 : UniformLower (data ⟨158, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_158 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_158) (rOuter := rOuter_158)
      (gapUpper := gapUpper_158)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_158
  · exact rEnclosed_158
  · exact gapUpperCheck_158
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
