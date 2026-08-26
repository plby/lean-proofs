import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk42
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk42
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk42
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 42. -/

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

def sincGapLower_042 : Rat := 285999 / 1000000

theorem sincGap_042 : UniformLower (data ⟨42, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_042 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_042) (rOuter := rOuter_042)
      (gapUpper := gapUpper_042)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_042
  · exact rEnclosed_042
  · exact gapUpperCheck_042
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
