import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk87
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk87
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk87
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 87. -/

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

def sincGapLower_087 : Rat := 277999 / 1000000

theorem sincGap_087 : UniformLower (data ⟨87, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_087 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_087) (rOuter := rOuter_087)
      (gapUpper := gapUpper_087)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_087
  · exact rEnclosed_087
  · exact gapUpperCheck_087
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
