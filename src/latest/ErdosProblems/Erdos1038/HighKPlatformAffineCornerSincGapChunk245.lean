import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk245
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk245
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk245
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 245. -/

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

def sincGapLower_245 : Rat := 211999 / 1000000

theorem sincGap_245 : UniformLower (data ⟨245, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_245 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_245) (rOuter := rOuter_245)
      (gapUpper := gapUpper_245)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_245
  · exact rEnclosed_245
  · exact gapUpperCheck_245
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
