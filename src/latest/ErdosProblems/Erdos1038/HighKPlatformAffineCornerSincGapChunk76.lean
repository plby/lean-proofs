import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk76
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk76
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk76
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 76. -/

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

def sincGapLower_076 : Rat := 279999 / 1000000

theorem sincGap_076 : UniformLower (data ⟨76, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_076 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_076) (rOuter := rOuter_076)
      (gapUpper := gapUpper_076)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_076
  · exact rEnclosed_076
  · exact gapUpperCheck_076
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
