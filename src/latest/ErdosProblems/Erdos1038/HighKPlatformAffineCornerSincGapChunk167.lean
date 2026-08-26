import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk167
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk167
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk167
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 167. -/

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

def sincGapLower_167 : Rat := 248999 / 1000000

theorem sincGap_167 : UniformLower (data ⟨167, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_167 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_167) (rOuter := rOuter_167)
      (gapUpper := gapUpper_167)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_167
  · exact rEnclosed_167
  · exact gapUpperCheck_167
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
