import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk136
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk136
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk136
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 136. -/

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

def sincGapLower_136 : Rat := 261999 / 1000000

theorem sincGap_136 : UniformLower (data ⟨136, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_136 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_136) (rOuter := rOuter_136)
      (gapUpper := gapUpper_136)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_136
  · exact rEnclosed_136
  · exact gapUpperCheck_136
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
