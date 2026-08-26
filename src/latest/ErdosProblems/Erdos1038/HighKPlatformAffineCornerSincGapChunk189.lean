import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk189
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk189
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk189
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 189. -/

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

def sincGapLower_189 : Rat := 238999 / 1000000

theorem sincGap_189 : UniformLower (data ⟨189, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_189 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_189) (rOuter := rOuter_189)
      (gapUpper := gapUpper_189)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_189
  · exact rEnclosed_189
  · exact gapUpperCheck_189
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
