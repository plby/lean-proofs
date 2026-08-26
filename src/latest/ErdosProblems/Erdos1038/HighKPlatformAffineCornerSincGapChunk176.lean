import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk176
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk176
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk176
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 176. -/

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

def sincGapLower_176 : Rat := 244999 / 1000000

theorem sincGap_176 : UniformLower (data ⟨176, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_176 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_176) (rOuter := rOuter_176)
      (gapUpper := gapUpper_176)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_176
  · exact rEnclosed_176
  · exact gapUpperCheck_176
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
