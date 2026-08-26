import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk92
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk92
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk92
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 92. -/

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

def sincGapLower_092 : Rat := 275999 / 1000000

theorem sincGap_092 : UniformLower (data ⟨92, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_092 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_092) (rOuter := rOuter_092)
      (gapUpper := gapUpper_092)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_092
  · exact rEnclosed_092
  · exact gapUpperCheck_092
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
