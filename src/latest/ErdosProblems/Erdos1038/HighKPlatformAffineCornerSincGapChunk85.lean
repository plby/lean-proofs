import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk85
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk85
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk85
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 85. -/

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

def sincGapLower_085 : Rat := 277999 / 1000000

theorem sincGap_085 : UniformLower (data ⟨85, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_085 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_085) (rOuter := rOuter_085)
      (gapUpper := gapUpper_085)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_085
  · exact rEnclosed_085
  · exact gapUpperCheck_085
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
