import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk117
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk117
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk117
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 117. -/

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

def sincGapLower_117 : Rat := 268999 / 1000000

theorem sincGap_117 : UniformLower (data ⟨117, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_117 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_117) (rOuter := rOuter_117)
      (gapUpper := gapUpper_117)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_117
  · exact rEnclosed_117
  · exact gapUpperCheck_117
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
