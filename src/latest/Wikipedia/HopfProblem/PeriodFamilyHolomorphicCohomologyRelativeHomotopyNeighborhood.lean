import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopyEquations
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisInverseApplicationIdentity

/-!
# A genuine local nonzero-mode potential for every closed smooth triple

One neighborhood of the original base point, chosen from the actual
period family alone, supports the selected-inverse potential of every
closed smooth triple. All three equations are equations of actual
differentiated smooth functions and remove precisely the original Haar
zero coefficients.
-/

noncomputable section

open TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy

open FourierParameter RelativeOperators

/-- A single original neighborhood solves every nonzero Fourier mode of
every genuinely closed smooth relative triple. -/
theorem exists_open_nonzero_mode_potential {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)
    (b₀ : U) :
    ∃ V : Opens ℂ, ∃ hVU : V ≤ U, (b₀ : ℂ) ∈ V ∧
      ∀ (a₀ : SmoothFamily U (Fin 4)) (a : Fin 2 → SmoothFamily U (Fin 4)),
        IsClosedTriple P a₀ a → ∃ g : SmoothFamily V (Fin 4),
          (∀ (b : V) (t : UnitAddTorus (Fin 4)),
            d0 g (b, t) = a₀ (Set.inclusion hVU b, t) - a₀.coefficientValue 0 (b : ℂ)) ∧
          ∀ (j : Fin 2) (b : V) (t : UnitAddTorus (Fin 4)),
            verticalOperator (restrictPeriods P hVU) j g (b, t) =
              a j (Set.inclusion hVU b, t) - (a j).coefficientValue 0 (b : ℂ) := by
  obtain ⟨V, hVU, hb, hm, hhol, hinverse, _⟩ :=
    FourierSynthesisInverse.exists_open_inverse_identity_data P b₀
  refine ⟨V, hVU, hb, ?_⟩
  intro a₀ a hclosed
  refine ⟨potentialOfFamilies P (P.point b₀) hVU a hm, ?_, ?_⟩
  · exact potentialOfFamilies_d0_apply P (P.point b₀) hVU a₀ a hm hinverse hhol hclosed
  · exact potentialOfFamilies_vertical_apply P (P.point b₀) hVU a₀ a hm hinverse hclosed

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy
