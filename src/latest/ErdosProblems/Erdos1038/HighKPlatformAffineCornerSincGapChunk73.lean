import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk73
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk73
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk73
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 73. -/

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

def sincGapLower_073 : Rat := 280999 / 1000000

theorem sincGap_073 : UniformLower (data ⟨73, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_073 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_073) (rOuter := rOuter_073)
      (gapUpper := gapUpper_073)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_073
  · exact rEnclosed_073
  · exact gapUpperCheck_073
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
