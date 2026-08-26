import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk14
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk14
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk14
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 14. -/

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

def sincGapLower_014 : Rat := 287999 / 1000000

theorem sincGap_014 : UniformLower (data ⟨14, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_014 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_014) (rOuter := rOuter_014)
      (gapUpper := gapUpper_014)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_014
  · exact rEnclosed_014
  · exact gapUpperCheck_014
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
