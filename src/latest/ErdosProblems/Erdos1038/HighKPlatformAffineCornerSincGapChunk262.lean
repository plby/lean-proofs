import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk262
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk262
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk262
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 262. -/

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

def sincGapLower_262 : Rat := 202999 / 1000000

theorem sincGap_262 : UniformLower (data ⟨262, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_262 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_262) (rOuter := rOuter_262)
      (gapUpper := gapUpper_262)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_262
  · exact rEnclosed_262
  · exact gapUpperCheck_262
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
