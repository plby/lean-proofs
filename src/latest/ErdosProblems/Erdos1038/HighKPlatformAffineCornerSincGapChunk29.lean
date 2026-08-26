import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk29
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk29
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk29
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 29. -/

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

def sincGapLower_029 : Rat := 286999 / 1000000

theorem sincGap_029 : UniformLower (data ⟨29, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_029 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_029) (rOuter := rOuter_029)
      (gapUpper := gapUpper_029)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_029
  · exact rEnclosed_029
  · exact gapUpperCheck_029
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
