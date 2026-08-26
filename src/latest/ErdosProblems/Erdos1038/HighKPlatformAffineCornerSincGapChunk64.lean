import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk64
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk64
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk64
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 64. -/

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

def sincGapLower_064 : Rat := 282999 / 1000000

theorem sincGap_064 : UniformLower (data ⟨64, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_064 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_064) (rOuter := rOuter_064)
      (gapUpper := gapUpper_064)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_064
  · exact rEnclosed_064
  · exact gapUpperCheck_064
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
