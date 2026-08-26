import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk79
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk79
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk79
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 79. -/

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

def sincGapLower_079 : Rat := 279999 / 1000000

theorem sincGap_079 : UniformLower (data ⟨79, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_079 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_079) (rOuter := rOuter_079)
      (gapUpper := gapUpper_079)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_079
  · exact rEnclosed_079
  · exact gapUpperCheck_079
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
