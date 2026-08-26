import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk26
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk26
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk26
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 26. -/

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

def sincGapLower_026 : Rat := 287999 / 1000000

theorem sincGap_026 : UniformLower (data ⟨26, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_026 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_026) (rOuter := rOuter_026)
      (gapUpper := gapUpper_026)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_026
  · exact rEnclosed_026
  · exact gapUpperCheck_026
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
