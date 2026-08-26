import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk190
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk190
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk190
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 190. -/

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

def sincGapLower_190 : Rat := 238999 / 1000000

theorem sincGap_190 : UniformLower (data ⟨190, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_190 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_190) (rOuter := rOuter_190)
      (gapUpper := gapUpper_190)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_190
  · exact rEnclosed_190
  · exact gapUpperCheck_190
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
