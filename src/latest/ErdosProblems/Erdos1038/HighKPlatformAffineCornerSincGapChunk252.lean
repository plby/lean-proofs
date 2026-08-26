import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk252
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk252
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk252
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 252. -/

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

def sincGapLower_252 : Rat := 207999 / 1000000

theorem sincGap_252 : UniformLower (data ⟨252, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_252 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_252) (rOuter := rOuter_252)
      (gapUpper := gapUpper_252)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_252
  · exact rEnclosed_252
  · exact gapUpperCheck_252
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
