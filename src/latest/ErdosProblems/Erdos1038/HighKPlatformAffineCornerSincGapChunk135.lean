import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk135
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk135
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk135
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 135. -/

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

def sincGapLower_135 : Rat := 261999 / 1000000

theorem sincGap_135 : UniformLower (data ⟨135, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_135 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_135) (rOuter := rOuter_135)
      (gapUpper := gapUpper_135)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_135
  · exact rEnclosed_135
  · exact gapUpperCheck_135
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
