import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk48
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk48
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk48
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 48. -/

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

def sincGapLower_048 : Rat := 284999 / 1000000

theorem sincGap_048 : UniformLower (data ⟨48, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_048 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_048) (rOuter := rOuter_048)
      (gapUpper := gapUpper_048)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_048
  · exact rEnclosed_048
  · exact gapUpperCheck_048
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
