import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk205
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk205
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk205
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 205. -/

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

def sincGapLower_205 : Rat := 231999 / 1000000

theorem sincGap_205 : UniformLower (data ⟨205, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_205 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_205) (rOuter := rOuter_205)
      (gapUpper := gapUpper_205)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_205
  · exact rEnclosed_205
  · exact gapUpperCheck_205
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
