import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk82
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk82
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk82
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 82. -/

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

def sincGapLower_082 : Rat := 278999 / 1000000

theorem sincGap_082 : UniformLower (data ⟨82, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_082 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_082) (rOuter := rOuter_082)
      (gapUpper := gapUpper_082)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_082
  · exact rEnclosed_082
  · exact gapUpperCheck_082
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
