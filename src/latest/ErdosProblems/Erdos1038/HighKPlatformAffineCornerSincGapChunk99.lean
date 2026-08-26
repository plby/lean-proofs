import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk99
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk99
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk99
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 99. -/

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

def sincGapLower_099 : Rat := 273999 / 1000000

theorem sincGap_099 : UniformLower (data ⟨99, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_099 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_099) (rOuter := rOuter_099)
      (gapUpper := gapUpper_099)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_099
  · exact rEnclosed_099
  · exact gapUpperCheck_099
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
