import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk199
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk199
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk199
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 199. -/

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

def sincGapLower_199 : Rat := 234999 / 1000000

theorem sincGap_199 : UniformLower (data ⟨199, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_199 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_199) (rOuter := rOuter_199)
      (gapUpper := gapUpper_199)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_199
  · exact rEnclosed_199
  · exact gapUpperCheck_199
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
