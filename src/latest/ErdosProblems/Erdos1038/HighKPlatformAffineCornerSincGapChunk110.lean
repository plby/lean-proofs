import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk110
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk110
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk110
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 110. -/

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

def sincGapLower_110 : Rat := 270999 / 1000000

theorem sincGap_110 : UniformLower (data ⟨110, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_110 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_110) (rOuter := rOuter_110)
      (gapUpper := gapUpper_110)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_110
  · exact rEnclosed_110
  · exact gapUpperCheck_110
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
