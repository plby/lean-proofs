import Wikipedia.HopfProblem.SpecialPeriodsUniquenessMu
import Wikipedia.HopfProblem.SpecialPeriodsUniquenessBeta

/-!
# Unconditional uniqueness of the actual special period functions

The normalized actual modular source and the original scalar generator
equations determine tau and the bounded middle period uniquely. The third
period is determined up to one complex constant under the original bound
on beta plus tau. All comparison functions below are the already
constructed coordinates of the actual admissible period map.
-/

noncomputable section

open UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods

open Triangle

/-- The source's full uniqueness assertion for scalar period functions.
The only hypotheses concern the competing functions; no uniformization,
special period, or analytic cusp model is supplied. -/
theorem specialPeriods_unique {τ μ β : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hpos : ∀ z : ℍ, 0 < (τ z).im)
    (hJ : ∀ z : ℍ, modularJ (ofComplex (τ z)) = 1728 * specialSourceCoordinate z)
    (hτ₁ : ∀ z : ℍ, τ (generatorOneSL • z) = (τ z - 1) / τ z)
    (hτ₂ : ∀ z : ℍ, τ (generatorTwoSL • z) = -1 / τ z)
    (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ)
    (hμ₁ : ∀ z : ℍ, μ (generatorOneSL • z) = (1 - μ z) / τ z)
    (hμ₂ : ∀ z : ℍ, μ (generatorTwoSL • z) = 1 + μ z / τ z)
    (hμb : IsBoundedAtImInfty μ)
    (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β)
    (hβ₁ : ∀ z : ℍ, β (generatorOneSL • z) = β z + 2 - 6 * (1 - μ z) ^ 2 / τ z)
    (hβ₂ : ∀ z : ℍ, β (generatorTwoSL • z) = β z - 3 - 6 * μ z ^ 2 / τ z)
    (hβb : IsBoundedAtImInfty (fun z => β z + τ z)) :
    τ = specialTau ∧ μ = specialMu ∧ ∃ c : ℂ, β = fun z => specialBeta z + c := by
  have hτeq := specialTau_unique hτ hpos hJ hτ₁ hτ₂
  subst τ
  have hμeq := specialMu_unique hμ hμ₁ hμ₂ hμb
  subst μ
  exact ⟨rfl, rfl, (specialBeta_solution_iff_eq_add_const β).mp ⟨hβ, hβ₁, hβ₂, hβb⟩⟩

end Wikipedia.HopfProblem.SpecialPeriods
