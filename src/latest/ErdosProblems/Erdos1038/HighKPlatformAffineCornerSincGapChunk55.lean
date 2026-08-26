import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk55
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk55
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk55
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 55. -/

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

def sincGapLower_055 : Rat := 283999 / 1000000

theorem sincGap_055 : UniformLower (data ⟨55, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_055 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_055) (rOuter := rOuter_055)
      (gapUpper := gapUpper_055)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_055
  · exact rEnclosed_055
  · exact gapUpperCheck_055
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
