import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk186
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk186
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk186
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 186. -/

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

def sincGapLower_186 : Rat := 240999 / 1000000

theorem sincGap_186 : UniformLower (data ⟨186, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_186 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_186) (rOuter := rOuter_186)
      (gapUpper := gapUpper_186)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_186
  · exact rEnclosed_186
  · exact gapUpperCheck_186
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
