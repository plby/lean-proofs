import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk53
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk53
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk53
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 53. -/

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

def sincGapLower_053 : Rat := 284999 / 1000000

theorem sincGap_053 : UniformLower (data ⟨53, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_053 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_053) (rOuter := rOuter_053)
      (gapUpper := gapUpper_053)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_053
  · exact rEnclosed_053
  · exact gapUpperCheck_053
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
