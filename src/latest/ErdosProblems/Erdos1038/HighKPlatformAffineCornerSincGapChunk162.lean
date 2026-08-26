import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk162
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk162
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk162
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 162. -/

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

def sincGapLower_162 : Rat := 250999 / 1000000

theorem sincGap_162 : UniformLower (data ⟨162, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_162 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_162) (rOuter := rOuter_162)
      (gapUpper := gapUpper_162)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_162
  · exact rEnclosed_162
  · exact gapUpperCheck_162
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
