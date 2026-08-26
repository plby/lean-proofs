import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk84
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk84
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk84
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 84. -/

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

def sincGapLower_084 : Rat := 277999 / 1000000

theorem sincGap_084 : UniformLower (data ⟨84, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_084 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_084) (rOuter := rOuter_084)
      (gapUpper := gapUpper_084)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_084
  · exact rEnclosed_084
  · exact gapUpperCheck_084
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
