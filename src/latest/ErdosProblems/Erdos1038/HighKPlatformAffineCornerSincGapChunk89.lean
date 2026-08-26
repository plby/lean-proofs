import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk89
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk89
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk89
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 89. -/

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

def sincGapLower_089 : Rat := 276999 / 1000000

theorem sincGap_089 : UniformLower (data ⟨89, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_089 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_089) (rOuter := rOuter_089)
      (gapUpper := gapUpper_089)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_089
  · exact rEnclosed_089
  · exact gapUpperCheck_089
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
