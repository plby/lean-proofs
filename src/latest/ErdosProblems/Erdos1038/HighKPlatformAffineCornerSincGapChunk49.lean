import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk49
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk49
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk49
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 49. -/

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

def sincGapLower_049 : Rat := 284999 / 1000000

theorem sincGap_049 : UniformLower (data ⟨49, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_049 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_049) (rOuter := rOuter_049)
      (gapUpper := gapUpper_049)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_049
  · exact rEnclosed_049
  · exact gapUpperCheck_049
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
