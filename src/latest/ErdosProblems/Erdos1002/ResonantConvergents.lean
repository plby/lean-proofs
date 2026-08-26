import ErdosProblems.Erdos1002.Resonances
import ErdosProblems.Erdos1002.ContinuedFractions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Recognition of primitive resonances as convergents

This is the exact interface between the rational-cell coordinates and
Legendre's theorem.  The coprimality condition is kept explicit, as it is in
the manuscript's primitive shot sum.
-/

namespace Erdos1002

noncomputable section

/-- A primitive nearest-cell resonance satisfying Legendre's sharp scaled
bound is a rational continued-fraction convergent. -/
theorem resonance_eq_convergent_of_small
    (α : ℝ) (p : ℕ) (hp : 0 < p)
    (hcop : Nat.Coprime (resonanceNumerator p α).natAbs p)
    (hsmall :
      |resonanceDelta p α| < 1 / (2 * (p : ℝ))) :
    ∃ n : ℕ,
      (resonanceNumerator p α : ℚ) / (p : ℚ) = α.convergent n := by
  apply intDivNat_eq_convergent_of_scaled α (resonanceNumerator p α) p hp hcop
  exact hsmall

/-- The same primitive-resonance recognition in mathlib's general
continued-fraction representation. -/
theorem convs_eq_resonance_of_small
    (α : ℝ) (p : ℕ) (hp : 0 < p)
    (hcop : Nat.Coprime (resonanceNumerator p α).natAbs p)
    (hsmall :
      |resonanceDelta p α| < 1 / (2 * (p : ℝ))) :
    ∃ n : ℕ,
      (GenContFract.of α).convs n =
        (((resonanceNumerator p α : ℚ) / (p : ℚ) : ℚ) : ℝ) := by
  apply convs_eq_intDivNat_of_scaled α (resonanceNumerator p α) p hp hcop
  exact hsmall

end

end Erdos1002
