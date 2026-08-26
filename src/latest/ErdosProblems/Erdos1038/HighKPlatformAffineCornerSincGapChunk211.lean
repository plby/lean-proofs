import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk211
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk211
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk211
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 211. -/

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

def sincGapLower_211 : Rat := 228999 / 1000000

theorem sincGap_211 : UniformLower (data ⟨211, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_211 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_211) (rOuter := rOuter_211)
      (gapUpper := gapUpper_211)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_211
  · exact rEnclosed_211
  · exact gapUpperCheck_211
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
