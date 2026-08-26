import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk40
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk40
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk40
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 40. -/

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

def sincGapLower_040 : Rat := 285999 / 1000000

theorem sincGap_040 : UniformLower (data ⟨40, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_040 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_040) (rOuter := rOuter_040)
      (gapUpper := gapUpper_040)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_040
  · exact rEnclosed_040
  · exact gapUpperCheck_040
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
