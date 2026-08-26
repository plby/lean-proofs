import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk258
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk258
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk258
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 258. -/

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

def sincGapLower_258 : Rat := 204999 / 1000000

theorem sincGap_258 : UniformLower (data ⟨258, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_258 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_258) (rOuter := rOuter_258)
      (gapUpper := gapUpper_258)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_258
  · exact rEnclosed_258
  · exact gapUpperCheck_258
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
