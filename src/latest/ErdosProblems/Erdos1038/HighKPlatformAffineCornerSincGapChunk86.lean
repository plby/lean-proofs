import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk86
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk86
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk86
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 86. -/

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

def sincGapLower_086 : Rat := 277999 / 1000000

theorem sincGap_086 : UniformLower (data ⟨86, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_086 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_086) (rOuter := rOuter_086)
      (gapUpper := gapUpper_086)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_086
  · exact rEnclosed_086
  · exact gapUpperCheck_086
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
