import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk168
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk168
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk168
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 168. -/

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

def sincGapLower_168 : Rat := 248999 / 1000000

theorem sincGap_168 : UniformLower (data ⟨168, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_168 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_168) (rOuter := rOuter_168)
      (gapUpper := gapUpper_168)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_168
  · exact rEnclosed_168
  · exact gapUpperCheck_168
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
