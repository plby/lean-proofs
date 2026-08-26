import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk196
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk196
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk196
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 196. -/

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

def sincGapLower_196 : Rat := 235999 / 1000000

theorem sincGap_196 : UniformLower (data ⟨196, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_196 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_196) (rOuter := rOuter_196)
      (gapUpper := gapUpper_196)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_196
  · exact rEnclosed_196
  · exact gapUpperCheck_196
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
