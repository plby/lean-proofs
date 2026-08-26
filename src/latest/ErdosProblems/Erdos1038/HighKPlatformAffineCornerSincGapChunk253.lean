import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk253
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk253
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk253
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 253. -/

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

def sincGapLower_253 : Rat := 207999 / 1000000

theorem sincGap_253 : UniformLower (data ⟨253, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_253 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_253) (rOuter := rOuter_253)
      (gapUpper := gapUpper_253)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_253
  · exact rEnclosed_253
  · exact gapUpperCheck_253
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
