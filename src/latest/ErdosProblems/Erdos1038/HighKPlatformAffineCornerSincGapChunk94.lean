import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk94
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk94
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk94
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 94. -/

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

def sincGapLower_094 : Rat := 275999 / 1000000

theorem sincGap_094 : UniformLower (data ⟨94, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_094 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_094) (rOuter := rOuter_094)
      (gapUpper := gapUpper_094)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_094
  · exact rEnclosed_094
  · exact gapUpperCheck_094
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
