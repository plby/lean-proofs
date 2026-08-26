import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk239
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk239
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk239
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 239. -/

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

def sincGapLower_239 : Rat := 214999 / 1000000

theorem sincGap_239 : UniformLower (data ⟨239, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_239 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_239) (rOuter := rOuter_239)
      (gapUpper := gapUpper_239)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_239
  · exact rEnclosed_239
  · exact gapUpperCheck_239
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
