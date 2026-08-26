import ErdosProblems.Erdos796.CertificateScore
import ErdosProblems.Erdos796.CofactorFunctional

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The certified lower bound for `Gamma`
-/

namespace Erdos796

/-- Once boundedness of the score set is established, the explicit compatible
family gives the manuscript's lower bound.  Boundedness is supplied by the
multiplicative-Sidon majorant developed separately. -/
theorem four_fifteenths_le_Gamma_of_bddAbove
    (hBdd : BddAbove gammaScores) :
    (4 : ℝ) / 15 ≤ Gamma := by
  rw [Gamma_eq_sSup_gammaScores]
  exact le_csSup hBdd four_fifteenths_mem_gamma_scores

/-- A uniform summable excess majorant simultaneously certifies score-set
boundedness and the lower bound. -/
theorem four_fifteenths_le_Gamma_of_uniform_majorant {B : ℕ → ℝ}
    (hBound : ∀ (U : ℕ → Finset ℕ), Compatible U →
      ∀ j : ℕ, excess U j ≤ B j)
    (hSummable : Summable (weightedMajorant B)) :
    (4 : ℝ) / 15 ≤ Gamma := by
  apply four_fifteenths_le_Gamma_of_bddAbove
  exact gammaScores_bddAbove_of_uniform_majorant hBound hSummable

end Erdos796
