import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk185
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk185
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk185
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 185. -/

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

def sincGapLower_185 : Rat := 240999 / 1000000

theorem sincGap_185 : UniformLower (data ⟨185, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_185 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_185) (rOuter := rOuter_185)
      (gapUpper := gapUpper_185)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_185
  · exact rEnclosed_185
  · exact gapUpperCheck_185
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
