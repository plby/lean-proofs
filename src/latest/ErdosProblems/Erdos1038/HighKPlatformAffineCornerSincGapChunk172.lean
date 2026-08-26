import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk172
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk172
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk172
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 172. -/

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

def sincGapLower_172 : Rat := 246999 / 1000000

theorem sincGap_172 : UniformLower (data ⟨172, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_172 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_172) (rOuter := rOuter_172)
      (gapUpper := gapUpper_172)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_172
  · exact rEnclosed_172
  · exact gapUpperCheck_172
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
