import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk215
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk215
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk215
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 215. -/

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

def sincGapLower_215 : Rat := 226999 / 1000000

theorem sincGap_215 : UniformLower (data ⟨215, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_215 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_215) (rOuter := rOuter_215)
      (gapUpper := gapUpper_215)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_215
  · exact rEnclosed_215
  · exact gapUpperCheck_215
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
