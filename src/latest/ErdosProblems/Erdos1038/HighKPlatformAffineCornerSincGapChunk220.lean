import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk220
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk220
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk220
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 220. -/

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

def sincGapLower_220 : Rat := 223999 / 1000000

theorem sincGap_220 : UniformLower (data ⟨220, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_220 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_220) (rOuter := rOuter_220)
      (gapUpper := gapUpper_220)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_220
  · exact rEnclosed_220
  · exact gapUpperCheck_220
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
