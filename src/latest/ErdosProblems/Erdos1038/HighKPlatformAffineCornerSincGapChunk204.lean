import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk204
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk204
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk204
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 204. -/

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

def sincGapLower_204 : Rat := 231999 / 1000000

theorem sincGap_204 : UniformLower (data ⟨204, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_204 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_204) (rOuter := rOuter_204)
      (gapUpper := gapUpper_204)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_204
  · exact rEnclosed_204
  · exact gapUpperCheck_204
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
