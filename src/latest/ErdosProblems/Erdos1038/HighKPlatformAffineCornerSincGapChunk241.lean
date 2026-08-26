import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk241
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk241
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk241
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 241. -/

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

def sincGapLower_241 : Rat := 213999 / 1000000

theorem sincGap_241 : UniformLower (data ⟨241, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_241 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_241) (rOuter := rOuter_241)
      (gapUpper := gapUpper_241)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_241
  · exact rEnclosed_241
  · exact gapUpperCheck_241
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
