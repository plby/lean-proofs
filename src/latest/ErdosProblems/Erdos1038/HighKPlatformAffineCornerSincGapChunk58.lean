import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk58
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk58
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk58
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 58. -/

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

def sincGapLower_058 : Rat := 283999 / 1000000

theorem sincGap_058 : UniformLower (data ⟨58, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_058 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_058) (rOuter := rOuter_058)
      (gapUpper := gapUpper_058)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_058
  · exact rEnclosed_058
  · exact gapUpperCheck_058
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
