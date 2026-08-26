import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk251
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk251
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk251
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 251. -/

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

def sincGapLower_251 : Rat := 208999 / 1000000

theorem sincGap_251 : UniformLower (data ⟨251, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_251 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_251) (rOuter := rOuter_251)
      (gapUpper := gapUpper_251)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_251
  · exact rEnclosed_251
  · exact gapUpperCheck_251
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
