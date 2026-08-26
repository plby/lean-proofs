import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk51
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk51
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk51
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 51. -/

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

def sincGapLower_051 : Rat := 284999 / 1000000

theorem sincGap_051 : UniformLower (data ⟨51, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_051 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_051) (rOuter := rOuter_051)
      (gapUpper := gapUpper_051)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_051
  · exact rEnclosed_051
  · exact gapUpperCheck_051
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
