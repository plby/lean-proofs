import ErdosProblems.Erdos796.StructuralFiniteBound
import ErdosProblems.Erdos796.CofactorModelLimitProof
import ErdosProblems.Erdos796.PrimeNumberTheoremProof
import ErdosProblems.Erdos796.SemiprimeAsymptoticProof
import ErdosProblems.Erdos796.GammaFinite
import ErdosProblems.Erdos796.GammaExplicitUpper
import ErdosProblems.Erdos796.MertensExplicitUpper

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Unconditional proof of the corrected Erdős 796 asymptotic

This module contains only the final assembly.  The structural reduction,
finite cofactor-model limit, prime number theorem, and second-order
semiprime asymptotic are proved in the imported modules.
-/

namespace Erdos796

/-- The baseline contribution has second-order constant `1 + M`. -/
theorem baselineAsymptotic : BaselineAsymptotic Mertens.M :=
  baselineAsymptotic_of_semiprime_and_pnt Mertens.M
    semiprimeAsymptotic primeNumberTheorem

/-- The corrected second-order asymptotic, with its variational constant. -/
theorem hasSecondOrderConstant :
    HasSecondOrderConstant (1 + Mertens.M + Gamma) :=
  hasSecondOrderConstant_of_components Mertens.M
    StructuralFiniteBound.structuralReduction
    (cofactorModelLimit_of_primeNumberTheorem primeNumberTheorem)
    baselineAsymptotic

/-- Erdős Problem 796 in the formal statement of `Statement.lean`. -/
theorem erdosProblem796 : ErdosProblem796 :=
  ⟨1 + Mertens.M + Gamma, hasSecondOrderConstant⟩

/-- The finite certificate and explicit majorant bracket the variational
correction appearing in the final constant. -/
theorem Gamma_bounds :
    (4 : ℝ) / 15 ≤ Gamma ∧ Gamma < 13 :=
  ⟨four_fifteenths_le_Gamma, Gamma_lt_thirteen⟩

/-- A fully explicit, kernel-checked upper bound for the
Meissel--Mertens constant used in the second-order term. -/
theorem MertensM_lt_one : Mertens.M < 1 :=
  mertensM_lt_933_div_1000.trans (by norm_num)

/-- The complete second-order constant in the main asymptotic is less
than `15`, as asserted in the manuscript. -/
theorem secondOrderConstant_lt_fifteen :
    1 + Mertens.M + Gamma < 15 := by
  linarith [mertensM_lt_933_div_1000, Gamma_lt_thirteen]

end Erdos796
