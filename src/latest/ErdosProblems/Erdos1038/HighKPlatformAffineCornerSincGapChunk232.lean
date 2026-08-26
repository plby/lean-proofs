import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk232
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk232
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk232
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 232. -/

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

def sincGapLower_232 : Rat := 218999 / 1000000

theorem sincGap_232 : UniformLower (data ⟨232, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_232 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_232) (rOuter := rOuter_232)
      (gapUpper := gapUpper_232)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_232
  · exact rEnclosed_232
  · exact gapUpperCheck_232
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
