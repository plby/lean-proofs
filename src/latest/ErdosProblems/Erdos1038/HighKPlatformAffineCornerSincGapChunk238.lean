import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk238
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk238
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk238
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 238. -/

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

def sincGapLower_238 : Rat := 215999 / 1000000

theorem sincGap_238 : UniformLower (data ⟨238, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_238 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_238) (rOuter := rOuter_238)
      (gapUpper := gapUpper_238)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_238
  · exact rEnclosed_238
  · exact gapUpperCheck_238
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
