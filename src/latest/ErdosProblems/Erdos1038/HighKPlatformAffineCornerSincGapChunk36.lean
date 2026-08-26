import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk36
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk36
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk36
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 36. -/

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

def sincGapLower_036 : Rat := 286999 / 1000000

theorem sincGap_036 : UniformLower (data ⟨36, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_036 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_036) (rOuter := rOuter_036)
      (gapUpper := gapUpper_036)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_036
  · exact rEnclosed_036
  · exact gapUpperCheck_036
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
