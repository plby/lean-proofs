import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk200
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk200
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk200
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 200. -/

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

def sincGapLower_200 : Rat := 233999 / 1000000

theorem sincGap_200 : UniformLower (data ⟨200, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_200 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_200) (rOuter := rOuter_200)
      (gapUpper := gapUpper_200)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_200
  · exact rEnclosed_200
  · exact gapUpperCheck_200
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
