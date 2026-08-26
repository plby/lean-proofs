import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk206
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk206
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk206
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 206. -/

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

def sincGapLower_206 : Rat := 230999 / 1000000

theorem sincGap_206 : UniformLower (data ⟨206, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_206 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_206) (rOuter := rOuter_206)
      (gapUpper := gapUpper_206)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_206
  · exact rEnclosed_206
  · exact gapUpperCheck_206
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
