import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk148
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk148
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk148
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 148. -/

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

def sincGapLower_148 : Rat := 256999 / 1000000

theorem sincGap_148 : UniformLower (data ⟨148, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_148 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_148) (rOuter := rOuter_148)
      (gapUpper := gapUpper_148)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_148
  · exact rEnclosed_148
  · exact gapUpperCheck_148
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
