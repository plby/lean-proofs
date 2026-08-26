import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk247
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk247
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk247
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 247. -/

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

def sincGapLower_247 : Rat := 210999 / 1000000

theorem sincGap_247 : UniformLower (data ⟨247, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_247 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_247) (rOuter := rOuter_247)
      (gapUpper := gapUpper_247)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_247
  · exact rEnclosed_247
  · exact gapUpperCheck_247
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
