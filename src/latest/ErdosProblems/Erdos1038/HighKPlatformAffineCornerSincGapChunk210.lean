import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk210
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk210
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk210
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 210. -/

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

def sincGapLower_210 : Rat := 228999 / 1000000

theorem sincGap_210 : UniformLower (data ⟨210, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_210 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_210) (rOuter := rOuter_210)
      (gapUpper := gapUpper_210)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_210
  · exact rEnclosed_210
  · exact gapUpperCheck_210
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
