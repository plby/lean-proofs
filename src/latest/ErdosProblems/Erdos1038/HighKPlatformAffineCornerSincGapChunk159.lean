import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk159
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk159
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk159
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 159. -/

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

def sincGapLower_159 : Rat := 251999 / 1000000

theorem sincGap_159 : UniformLower (data ⟨159, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_159 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_159) (rOuter := rOuter_159)
      (gapUpper := gapUpper_159)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_159
  · exact rEnclosed_159
  · exact gapUpperCheck_159
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
