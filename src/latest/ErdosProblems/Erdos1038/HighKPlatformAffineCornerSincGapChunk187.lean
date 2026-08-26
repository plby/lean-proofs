import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk187
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk187
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk187
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 187. -/

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

def sincGapLower_187 : Rat := 239999 / 1000000

theorem sincGap_187 : UniformLower (data ⟨187, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_187 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_187) (rOuter := rOuter_187)
      (gapUpper := gapUpper_187)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_187
  · exact rEnclosed_187
  · exact gapUpperCheck_187
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
