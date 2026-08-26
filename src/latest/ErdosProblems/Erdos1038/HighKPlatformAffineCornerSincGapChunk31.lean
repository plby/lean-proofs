import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk31
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk31
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk31
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 31. -/

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

def sincGapLower_031 : Rat := 286999 / 1000000

theorem sincGap_031 : UniformLower (data ⟨31, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_031 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_031) (rOuter := rOuter_031)
      (gapUpper := gapUpper_031)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_031
  · exact rEnclosed_031
  · exact gapUpperCheck_031
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
