import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk132
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk132
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk132
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 132. -/

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

def sincGapLower_132 : Rat := 262999 / 1000000

theorem sincGap_132 : UniformLower (data ⟨132, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_132 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_132) (rOuter := rOuter_132)
      (gapUpper := gapUpper_132)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_132
  · exact rEnclosed_132
  · exact gapUpperCheck_132
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
