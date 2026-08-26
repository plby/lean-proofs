import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk130
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk130
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk130
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 130. -/

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

def sincGapLower_130 : Rat := 263999 / 1000000

theorem sincGap_130 : UniformLower (data ⟨130, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_130 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_130) (rOuter := rOuter_130)
      (gapUpper := gapUpper_130)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_130
  · exact rEnclosed_130
  · exact gapUpperCheck_130
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
