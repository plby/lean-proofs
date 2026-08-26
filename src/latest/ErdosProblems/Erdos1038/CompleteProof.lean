import ErdosProblems.Erdos1038.HighKPlatformAffineTable
import ErdosProblems.Erdos1038.HighKTerminalBaseCertificate
import ErdosProblems.Erdos1038.HighKPlatformConstantIntegratedReduction

/-!
# Parameter-free completion of Erdős problem 1038

The two finite numerical tables imported above discharge the last affine
and terminal scalar leaves.  All analytic, normalization, extremal, and
equality-case arguments are assembled by the exact reduction theorem.
-/

set_option warningAsError false

namespace Erdos1038

/-- The complete formal statement of Erdős problem 1038. -/
theorem mainTheorem : MainTheorem :=
  mainTheorem_of_affine_and_terminalBase
    highKAffineGlobalCalibrationCertificate
    highKTerminalBaseCertificate

end Erdos1038
