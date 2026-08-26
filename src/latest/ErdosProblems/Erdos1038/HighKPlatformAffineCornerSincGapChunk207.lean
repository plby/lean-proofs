import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk207
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk207
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk207
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 207. -/

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

def sincGapLower_207 : Rat := 230999 / 1000000

theorem sincGap_207 : UniformLower (data ⟨207, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_207 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_207) (rOuter := rOuter_207)
      (gapUpper := gapUpper_207)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_207
  · exact rEnclosed_207
  · exact gapUpperCheck_207
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
