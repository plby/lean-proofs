import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk193
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk193
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk193
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 193. -/

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

def sincGapLower_193 : Rat := 236999 / 1000000

theorem sincGap_193 : UniformLower (data ⟨193, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_193 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_193) (rOuter := rOuter_193)
      (gapUpper := gapUpper_193)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_193
  · exact rEnclosed_193
  · exact gapUpperCheck_193
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
