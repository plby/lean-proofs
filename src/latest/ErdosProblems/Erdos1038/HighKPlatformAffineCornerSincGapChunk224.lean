import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk224
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk224
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk224
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 224. -/

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

def sincGapLower_224 : Rat := 221999 / 1000000

theorem sincGap_224 : UniformLower (data ⟨224, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_224 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_224) (rOuter := rOuter_224)
      (gapUpper := gapUpper_224)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_224
  · exact rEnclosed_224
  · exact gapUpperCheck_224
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
