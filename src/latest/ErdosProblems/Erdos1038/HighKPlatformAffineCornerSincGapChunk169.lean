import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk169
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk169
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk169
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 169. -/

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

def sincGapLower_169 : Rat := 247999 / 1000000

theorem sincGap_169 : UniformLower (data ⟨169, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_169 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_169) (rOuter := rOuter_169)
      (gapUpper := gapUpper_169)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_169
  · exact rEnclosed_169
  · exact gapUpperCheck_169
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
