import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk191
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk191
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk191
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 191. -/

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

def sincGapLower_191 : Rat := 237999 / 1000000

theorem sincGap_191 : UniformLower (data ⟨191, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_191 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_191) (rOuter := rOuter_191)
      (gapUpper := gapUpper_191)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_191
  · exact rEnclosed_191
  · exact gapUpperCheck_191
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
