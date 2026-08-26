import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk165
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk165
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk165
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 165. -/

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

def sincGapLower_165 : Rat := 249999 / 1000000

theorem sincGap_165 : UniformLower (data ⟨165, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_165 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_165) (rOuter := rOuter_165)
      (gapUpper := gapUpper_165)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_165
  · exact rEnclosed_165
  · exact gapUpperCheck_165
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
