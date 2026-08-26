import ErdosProblems.Erdos1038.HighKPlatformConstantGlobalCertificate
import ErdosProblems.Erdos1038.HighKTerminalRatioCertificate

/-!
# Final reduction after closing the constant and terminal-range regimes
-/

set_option warningAsError false

namespace Erdos1038

noncomputable section

/-- With the 840-cell constant table and terminal ratio range now
unconditional, only the affine table, terminal base scalar charts, and the
uniform finite-jump theorem remain. -/
theorem mainTheorem_of_affine_terminalBase_and_uniformFiniteJump
    (haffine : HighKAffineGlobalCalibrationCertificate)
    (hterminalBase : HighKTerminalBaseCertificate)
    (hfiniteJump : PlatformResidualMaterialUniformFiniteJumpCertificate) :
    MainTheorem :=
  mainTheorem_of_affine_constant_terminalBase_and_uniformFiniteJump
    haffine highKConstantGlobalCalibrationCertificate hterminalBase hfiniteJump

/-- The constant table, terminal ratio cover, and finite-jump analysis are
all unconditional; only the affine table and terminal base charts remain. -/
theorem mainTheorem_of_affine_and_terminalBase
    (haffine : HighKAffineGlobalCalibrationCertificate)
    (hterminalBase : HighKTerminalBaseCertificate) :
    MainTheorem :=
  mainTheorem_of_affine_constant_terminalBase haffine
    highKConstantGlobalCalibrationCertificate hterminalBase

end

end Erdos1038
