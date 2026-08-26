import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk263
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk263
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk263
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 263. -/

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

def sincGapLower_263 : Rat := 202999 / 1000000

theorem sincGap_263 : UniformLower (data ⟨263, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_263 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_263) (rOuter := rOuter_263)
      (gapUpper := gapUpper_263)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_263
  · exact rEnclosed_263
  · exact gapUpperCheck_263
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
