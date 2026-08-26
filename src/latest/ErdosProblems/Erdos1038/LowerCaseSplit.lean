import ErdosProblems.Erdos1038.AtomizationReduction
import ErdosProblems.Erdos1038.LowKPolynomial
import ErdosProblems.Erdos1038.PureEndpointCase

/-!
# Global reduction to the high-ratio lower-bound case

For an arbitrary admissible polynomial, orientation and simultaneous
atomization produce an endpoint-normalized representative with no larger
sublevel volume.  The pure-endpoint and elementary-ratio branches already
have length at least `2`; only a nonempty residual configuration with
`k > 29/20` remains.
-/

open scoped ENNReal
open Polynomial

namespace Erdos1038

noncomputable section

theorem admissible_low_or_high_endpoint_split {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    ENNReal.ofReal 2 ≤ sublevelVolume f ∨
      ∃ g : Polynomial ℝ, ∃ h : EndpointNormalizationHypotheses g,
        sublevelVolume g ≤ sublevelVolume f ∧
          endpointResidualRoots h.normalizedPolynomial ≠ 0 ∧
          29 / 20 < normalizedEndpointResidualRatio h := by
  obtain ⟨g, ⟨h⟩, hvolume⟩ :=
    exists_endpointNormalization_le_of_admissible hf
  by_cases hreszero : endpointResidualRoots h.normalizedPolynomial = 0
  · left
    rw [← h.sublevelVolume_eq_two_of_residual_eq_zero hreszero]
    exact hvolume
  · rcases le_or_gt (normalizedEndpointResidualRatio h) (29 / 20) with
      hk | hk
    · left
      exact (h.ofReal_two_lt_sublevelVolume_of_lowK hreszero hk).le.trans
        hvolume
    · exact Or.inr ⟨g, h, hvolume, hreszero, hk⟩

theorem exists_high_endpointNormalization_of_sublevelVolume_lt_two
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hsmall : sublevelVolume f < ENNReal.ofReal 2) :
    ∃ g : Polynomial ℝ, ∃ h : EndpointNormalizationHypotheses g,
      sublevelVolume g ≤ sublevelVolume f ∧
        endpointResidualRoots h.normalizedPolynomial ≠ 0 ∧
        29 / 20 < normalizedEndpointResidualRatio h := by
  rcases admissible_low_or_high_endpoint_split hf with htwo | hhigh
  · exact False.elim (not_lt_of_ge htwo hsmall)
  · exact hhigh

end

end Erdos1038
