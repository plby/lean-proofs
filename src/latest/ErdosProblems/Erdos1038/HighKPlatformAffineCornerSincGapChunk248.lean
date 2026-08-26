import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk248
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk248
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk248
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 248. -/

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

def sincGapLower_248 : Rat := 209999 / 1000000

theorem sincGap_248 : UniformLower (data ⟨248, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_248 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_248) (rOuter := rOuter_248)
      (gapUpper := gapUpper_248)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_248
  · exact rEnclosed_248
  · exact gapUpperCheck_248
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
