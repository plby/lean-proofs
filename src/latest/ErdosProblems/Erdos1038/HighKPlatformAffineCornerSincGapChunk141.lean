import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk141
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk141
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk141
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 141. -/

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

def sincGapLower_141 : Rat := 259999 / 1000000

theorem sincGap_141 : UniformLower (data ⟨141, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_141 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_141) (rOuter := rOuter_141)
      (gapUpper := gapUpper_141)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_141
  · exact rEnclosed_141
  · exact gapUpperCheck_141
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
