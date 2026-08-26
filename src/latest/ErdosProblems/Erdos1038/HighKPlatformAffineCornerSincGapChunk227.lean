import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk227
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk227
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk227
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 227. -/

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

def sincGapLower_227 : Rat := 220999 / 1000000

theorem sincGap_227 : UniformLower (data ⟨227, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_227 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_227) (rOuter := rOuter_227)
      (gapUpper := gapUpper_227)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_227
  · exact rEnclosed_227
  · exact gapUpperCheck_227
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
