import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk34
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk34
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk34
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 34. -/

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

def sincGapLower_034 : Rat := 286999 / 1000000

theorem sincGap_034 : UniformLower (data ⟨34, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_034 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_034) (rOuter := rOuter_034)
      (gapUpper := gapUpper_034)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_034
  · exact rEnclosed_034
  · exact gapUpperCheck_034
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
