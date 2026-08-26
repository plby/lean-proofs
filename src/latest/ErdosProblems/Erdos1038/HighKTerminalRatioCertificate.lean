import ErdosProblems.Erdos1038.HighKPlatformNumericalCoverReduction
import ErdosProblems.Erdos1038.HighKTerminalRatioAnalysis

/-!
# Unconditional terminal ratio cover

This adapter discharges the terminal range leaf of the final numerical
reduction from the exact analytic argument in
`HighKTerminalRatioAnalysis`.
-/

set_option warningAsError false

namespace Erdos1038

noncomputable section

/-- The terminal parametrization covers every ratio beyond `21/5`. -/
theorem highKTerminalRatioCover_certificate : HighKTerminalRatioCover := by
  intro k hk
  exact exists_terminalPlatformRatio_eq_of_twenty_one_fifths_lt hk

/-- With the terminal range discharged, the final theorem has exactly four
remaining independent certificate inputs. -/
theorem mainTheorem_of_affine_constant_terminalBase_and_uniformFiniteJump
    (haffine : HighKAffineGlobalCalibrationCertificate)
    (hconstant : HighKConstantGlobalCalibrationCertificate)
    (hterminalBase : HighKTerminalBaseCertificate)
    (hfiniteJump : PlatformResidualMaterialUniformFiniteJumpCertificate) :
    MainTheorem :=
  mainTheorem_of_completePlatformRegimeCertificates haffine hconstant
    highKTerminalRatioCover_certificate hterminalBase hfiniteJump

/-- After the analytic finite-jump closure and terminal ratio argument, only
the affine table, constant table, and terminal base charts remain. -/
theorem mainTheorem_of_affine_constant_terminalBase
    (haffine : HighKAffineGlobalCalibrationCertificate)
    (hconstant : HighKConstantGlobalCalibrationCertificate)
    (hterminalBase : HighKTerminalBaseCertificate) :
    MainTheorem :=
  mainTheorem_of_completePlatformRegimes haffine hconstant
    highKTerminalRatioCover_certificate hterminalBase

end

end Erdos1038
