import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk175
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk175
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk175
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 175. -/

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

def sincGapLower_175 : Rat := 245999 / 1000000

theorem sincGap_175 : UniformLower (data ⟨175, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_175 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_175) (rOuter := rOuter_175)
      (gapUpper := gapUpper_175)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_175
  · exact rEnclosed_175
  · exact gapUpperCheck_175
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
