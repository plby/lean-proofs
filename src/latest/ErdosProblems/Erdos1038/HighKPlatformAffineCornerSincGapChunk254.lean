import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk254
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk254
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk254
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 254. -/

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

def sincGapLower_254 : Rat := 206999 / 1000000

theorem sincGap_254 : UniformLower (data ⟨254, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_254 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_254) (rOuter := rOuter_254)
      (gapUpper := gapUpper_254)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_254
  · exact rEnclosed_254
  · exact gapUpperCheck_254
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
