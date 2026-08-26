import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk105
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk105
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk105
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 105. -/

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

def sincGapLower_105 : Rat := 271999 / 1000000

theorem sincGap_105 : UniformLower (data ⟨105, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_105 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_105) (rOuter := rOuter_105)
      (gapUpper := gapUpper_105)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_105
  · exact rEnclosed_105
  · exact gapUpperCheck_105
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
