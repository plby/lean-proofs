import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk22
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk22
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk22
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 22. -/

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

def sincGapLower_022 : Rat := 287999 / 1000000

theorem sincGap_022 : UniformLower (data ⟨22, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_022 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_022) (rOuter := rOuter_022)
      (gapUpper := gapUpper_022)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_022
  · exact rEnclosed_022
  · exact gapUpperCheck_022
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
