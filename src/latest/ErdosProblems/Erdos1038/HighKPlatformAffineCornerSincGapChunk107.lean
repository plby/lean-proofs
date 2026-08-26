import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk107
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk107
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk107
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 107. -/

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

def sincGapLower_107 : Rat := 271999 / 1000000

theorem sincGap_107 : UniformLower (data ⟨107, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_107 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_107) (rOuter := rOuter_107)
      (gapUpper := gapUpper_107)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_107
  · exact rEnclosed_107
  · exact gapUpperCheck_107
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
