import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk139
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk139
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk139
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 139. -/

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

def sincGapLower_139 : Rat := 260999 / 1000000

theorem sincGap_139 : UniformLower (data ⟨139, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_139 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_139) (rOuter := rOuter_139)
      (gapUpper := gapUpper_139)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_139
  · exact rEnclosed_139
  · exact gapUpperCheck_139
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
