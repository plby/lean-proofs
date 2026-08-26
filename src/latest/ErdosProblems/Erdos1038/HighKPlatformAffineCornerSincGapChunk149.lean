import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk149
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk149
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk149
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 149. -/

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

def sincGapLower_149 : Rat := 256999 / 1000000

theorem sincGap_149 : UniformLower (data ⟨149, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_149 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_149) (rOuter := rOuter_149)
      (gapUpper := gapUpper_149)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_149
  · exact rEnclosed_149
  · exact gapUpperCheck_149
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
