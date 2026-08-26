import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk18
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk18
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk18
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 18. -/

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

def sincGapLower_018 : Rat := 287999 / 1000000

theorem sincGap_018 : UniformLower (data ⟨18, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_018 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_018) (rOuter := rOuter_018)
      (gapUpper := gapUpper_018)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_018
  · exact rEnclosed_018
  · exact gapUpperCheck_018
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
