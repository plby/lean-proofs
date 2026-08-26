import ErdosProblems.Erdos1038.HighKPlatformConstantTableCertificate
import ErdosProblems.Erdos1038.HighKPlatformNumericalCoverReduction
import ErdosProblems.Erdos1038.OneCutGlobalCertificate

/-!
# Closed constant-regime high-k certificate

This thin adapter instantiates the generated 840-cell table at the exact
target length `L` and exposes the proposition consumed by the final numerical
cover assembly.
-/

set_option warningAsError false

namespace Erdos1038

noncomputable section

open Set RatInterval
open HighKPlatformFormula
open HighKPlatformGlobalCrossingProbes
open HighKPlatformGlobalCrossingCertificates
open HighKPlatformConstantCell
open HighKPlatformConstantTableCertificate

/-- The target length belongs to the rigorous enclosure used by every
generated constant-edge scalar check. -/
theorem L_mem_highKConstantEllBox : ellBox.Contains L := by
  have hbounds :
      (1834430475762661 / 10 ^ 15 : ℝ) ≤ L ∧
        L ≤ (1834430475762662 / 10 ^ 15 : ℝ) :=
    ⟨oneCut_global_certificate.2.2.2.2.1.le,
      oneCut_global_certificate.2.2.2.2.2.le⟩
  simpa [ellBox, RatInterval.Contains] using! hbounds

/-- Exact calibration on the global constant crossing pair for the complete
interval `21/10 ≤ k ≤ 21/5`. -/
theorem highKConstantGlobalCalibrationCertificate :
    HighKConstantGlobalCalibrationCertificate := by
  intro k
  let kg : Icc (gridStart : ℝ) (gridEnd : ℝ) :=
    ⟨k, by
      simpa [gridStart, gridEnd, constantKBox] using! k.property⟩
  have h := constantCalibration_on_fullRange L_mem_highKConstantEllBox kg
  simpa [asGlobalParameter, kg] using! h

end

end Erdos1038
