import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk5
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk5
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk5
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 5. -/

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

def sincGapLower_005 : Rat := 287999 / 1000000

theorem sincGap_005 : UniformLower (data ⟨5, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_005 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_005) (rOuter := rOuter_005)
      (gapUpper := gapUpper_005)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_005
  · exact rEnclosed_005
  · exact gapUpperCheck_005
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
