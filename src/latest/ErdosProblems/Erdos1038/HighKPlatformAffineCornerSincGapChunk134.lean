import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk134
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk134
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk134
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 134. -/

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

def sincGapLower_134 : Rat := 261999 / 1000000

theorem sincGap_134 : UniformLower (data ⟨134, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_134 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_134) (rOuter := rOuter_134)
      (gapUpper := gapUpper_134)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_134
  · exact rEnclosed_134
  · exact gapUpperCheck_134
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
