import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk244
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk244
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk244
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 244. -/

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

def sincGapLower_244 : Rat := 211999 / 1000000

theorem sincGap_244 : UniformLower (data ⟨244, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_244 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_244) (rOuter := rOuter_244)
      (gapUpper := gapUpper_244)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_244
  · exact rEnclosed_244
  · exact gapUpperCheck_244
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
