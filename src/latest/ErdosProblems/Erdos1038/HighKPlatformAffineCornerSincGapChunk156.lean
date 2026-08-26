import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk156
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk156
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk156
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 156. -/

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

def sincGapLower_156 : Rat := 253999 / 1000000

theorem sincGap_156 : UniformLower (data ⟨156, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_156 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_156) (rOuter := rOuter_156)
      (gapUpper := gapUpper_156)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_156
  · exact rEnclosed_156
  · exact gapUpperCheck_156
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
