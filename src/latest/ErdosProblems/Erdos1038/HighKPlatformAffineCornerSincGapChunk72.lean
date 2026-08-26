import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk72
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk72
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk72
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 72. -/

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

def sincGapLower_072 : Rat := 280999 / 1000000

theorem sincGap_072 : UniformLower (data ⟨72, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_072 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_072) (rOuter := rOuter_072)
      (gapUpper := gapUpper_072)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_072
  · exact rEnclosed_072
  · exact gapUpperCheck_072
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
