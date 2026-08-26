import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk218
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk218
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk218
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 218. -/

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

def sincGapLower_218 : Rat := 224999 / 1000000

theorem sincGap_218 : UniformLower (data ⟨218, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_218 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_218) (rOuter := rOuter_218)
      (gapUpper := gapUpper_218)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_218
  · exact rEnclosed_218
  · exact gapUpperCheck_218
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
