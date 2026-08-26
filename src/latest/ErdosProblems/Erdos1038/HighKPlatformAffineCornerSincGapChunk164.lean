import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk164
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk164
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk164
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 164. -/

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

def sincGapLower_164 : Rat := 249999 / 1000000

theorem sincGap_164 : UniformLower (data ⟨164, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_164 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_164) (rOuter := rOuter_164)
      (gapUpper := gapUpper_164)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_164
  · exact rEnclosed_164
  · exact gapUpperCheck_164
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
