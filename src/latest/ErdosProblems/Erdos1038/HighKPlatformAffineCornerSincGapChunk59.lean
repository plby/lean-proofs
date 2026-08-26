import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk59
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk59
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk59
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 59. -/

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

def sincGapLower_059 : Rat := 283999 / 1000000

theorem sincGap_059 : UniformLower (data ⟨59, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_059 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_059) (rOuter := rOuter_059)
      (gapUpper := gapUpper_059)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_059
  · exact rEnclosed_059
  · exact gapUpperCheck_059
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
