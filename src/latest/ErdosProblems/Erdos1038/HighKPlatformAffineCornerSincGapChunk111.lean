import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk111
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk111
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk111
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 111. -/

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

def sincGapLower_111 : Rat := 270999 / 1000000

theorem sincGap_111 : UniformLower (data ⟨111, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_111 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_111) (rOuter := rOuter_111)
      (gapUpper := gapUpper_111)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_111
  · exact rEnclosed_111
  · exact gapUpperCheck_111
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
