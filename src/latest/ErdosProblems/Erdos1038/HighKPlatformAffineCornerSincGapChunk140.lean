import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk140
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk140
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk140
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 140. -/

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

def sincGapLower_140 : Rat := 259999 / 1000000

theorem sincGap_140 : UniformLower (data ⟨140, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_140 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_140) (rOuter := rOuter_140)
      (gapUpper := gapUpper_140)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_140
  · exact rEnclosed_140
  · exact gapUpperCheck_140
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
