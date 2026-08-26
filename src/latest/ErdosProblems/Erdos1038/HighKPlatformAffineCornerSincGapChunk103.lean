import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk103
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk103
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk103
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 103. -/

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

def sincGapLower_103 : Rat := 272999 / 1000000

theorem sincGap_103 : UniformLower (data ⟨103, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_103 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_103) (rOuter := rOuter_103)
      (gapUpper := gapUpper_103)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_103
  · exact rEnclosed_103
  · exact gapUpperCheck_103
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
