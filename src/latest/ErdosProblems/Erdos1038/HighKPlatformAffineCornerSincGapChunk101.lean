import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk101
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk101
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk101
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 101. -/

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

def sincGapLower_101 : Rat := 273999 / 1000000

theorem sincGap_101 : UniformLower (data ⟨101, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_101 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_101) (rOuter := rOuter_101)
      (gapUpper := gapUpper_101)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_101
  · exact rEnclosed_101
  · exact gapUpperCheck_101
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
