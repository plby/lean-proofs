import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk144
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk144
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk144
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 144. -/

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

def sincGapLower_144 : Rat := 258999 / 1000000

theorem sincGap_144 : UniformLower (data ⟨144, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_144 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_144) (rOuter := rOuter_144)
      (gapUpper := gapUpper_144)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_144
  · exact rEnclosed_144
  · exact gapUpperCheck_144
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
