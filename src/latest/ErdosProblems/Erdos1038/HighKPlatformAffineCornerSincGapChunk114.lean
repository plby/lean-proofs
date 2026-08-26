import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk114
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk114
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk114
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 114. -/

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

def sincGapLower_114 : Rat := 269999 / 1000000

theorem sincGap_114 : UniformLower (data ⟨114, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_114 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_114) (rOuter := rOuter_114)
      (gapUpper := gapUpper_114)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_114
  · exact rEnclosed_114
  · exact gapUpperCheck_114
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
