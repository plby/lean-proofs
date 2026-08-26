import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk21
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk21
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk21
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 21. -/

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

def sincGapLower_021 : Rat := 287999 / 1000000

theorem sincGap_021 : UniformLower (data ⟨21, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_021 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_021) (rOuter := rOuter_021)
      (gapUpper := gapUpper_021)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_021
  · exact rEnclosed_021
  · exact gapUpperCheck_021
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
