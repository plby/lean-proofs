import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk235
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk235
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk235
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 235. -/

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

def sincGapLower_235 : Rat := 216999 / 1000000

theorem sincGap_235 : UniformLower (data ⟨235, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_235 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_235) (rOuter := rOuter_235)
      (gapUpper := gapUpper_235)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_235
  · exact rEnclosed_235
  · exact gapUpperCheck_235
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
