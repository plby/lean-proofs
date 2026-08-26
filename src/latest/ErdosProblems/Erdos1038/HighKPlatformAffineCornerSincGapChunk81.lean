import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk81
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk81
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk81
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 81. -/

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

def sincGapLower_081 : Rat := 278999 / 1000000

theorem sincGap_081 : UniformLower (data ⟨81, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_081 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_081) (rOuter := rOuter_081)
      (gapUpper := gapUpper_081)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_081
  · exact rEnclosed_081
  · exact gapUpperCheck_081
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
