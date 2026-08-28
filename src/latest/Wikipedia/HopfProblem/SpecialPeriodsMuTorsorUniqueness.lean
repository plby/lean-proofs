import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorDivision
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorUniquenessCusp
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorUniquenessCompact

/-!
# Uniqueness of cusp-regular special μ functions

The difference of two affine special-period functions is homogeneous.
The actual elliptic divisor permits global holomorphic division by the
homogeneous generator.  Its simple cusp pole makes that invariant quotient
extend with value zero at the actual cusp.  Holomorphic descent and the
proved compact-curve vanishing theorem then force the difference to vanish.

Every analytic and geometric assertion used for the quotient is proved in
the imported construction; no uniqueness, global factor, descent, or
compact extension is a premise of the theorems below.
-/

noncomputable section

open Filter Set UpperHalfPlane
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

/-- A homogeneous holomorphic section regular at the actual cusp is
zero.  The denominator hypotheses describe its genuine elliptic divisor
and simple cusp pole, and are separately instantiated by the actual
Eisenstein generator construction. -/
theorem homogeneous_eq_zero_of_cuspRegular {τ : ℍ → ℍ} {ν F : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (hνc : CuspRegular ν)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = -F z / (τ z : ℂ))
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))
    (hFzero : ∀ z : ℍ, F z = 0 ↔
      triangleOrbitProjection z = triangleOrbitCenterOne ∨
        triangleOrbitProjection z = triangleOrbitCenterTwo)
    (hForder₁ : analyticOrderAt (F ∘ ofComplex) (Triangle.centerOne : ℂ) = 2)
    (hForder₂ : analyticOrderAt (F ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1)
    (hFcusp : ∃ v : ℂ → ℂ, AnalyticAt ℂ v 0 ∧ v 0 ≠ 0 ∧
      ∀ᶠ z in atImInfty, F z = (Triangle.cuspQ z)⁻¹ * v (Triangle.cuspQ z)) :
    ν = 0 := by
  obtain ⟨H, hH, hInv, hfactor⟩ := Division.exists_holomorphic_invariant_factor
    hτ hτc hν hν₁ hν₂ hF hF₁ hF₂ hFzero hForder₁ hForder₂
  obtain ⟨v, hv, hv0, hFv⟩ := hFcusp
  obtain ⟨g, hg, hg0, hHg⟩ := factor_cusp_germ hνc hv hv0 hFv hfactor
  have hH0 : H = 0 := invariant_eq_zero_of_eventually_cusp hH hInv hg hg0 hHg
  funext z
  calc
    ν z = F z * H z := hfactor z
    _ = 0 := by simp only [hH0, Pi.zero_apply, mul_zero]

/-- The two actual affine source laws give precisely the homogeneous
laws for the difference, with the first negative and the second positive. -/
theorem affine_sub_homogeneous {τ : ℍ → ℍ} {μ μ' : ℍ → ℂ}
    (hμ₁ : ∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (hμ₂ : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (hμ'₁ : ∀ z : ℍ, μ' (Triangle.generatorOneSL • z) = (1 - μ' z) / (τ z : ℂ))
    (hμ'₂ : ∀ z : ℍ, μ' (Triangle.generatorTwoSL • z) = 1 + μ' z / (τ z : ℂ)) :
    (∀ z : ℍ, (μ - μ') (Triangle.generatorOneSL • z) = -(μ - μ') z / (τ z : ℂ)) ∧
      (∀ z : ℍ, (μ - μ') (Triangle.generatorTwoSL • z) = (μ - μ') z / (τ z : ℂ)) := by
  constructor
  · intro z
    simp only [Pi.sub_apply, hμ₁ z, hμ'₁ z]
    ring
  · intro z
    simp only [Pi.sub_apply, hμ₂ z, hμ'₂ z]
    ring

/-- Two holomorphic affine special-period functions with analytic germs
at the actual cusp are equal.  The proof constructs their homogeneous
quotient and its zero compact extension, rather than assuming either. -/
theorem affine_eq_of_cuspRegular {τ : ℍ → ℍ} {μ μ' F : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ)
    (hμ' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ')
    (hμ₁ : ∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (hμ₂ : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (hμ'₁ : ∀ z : ℍ, μ' (Triangle.generatorOneSL • z) = (1 - μ' z) / (τ z : ℂ))
    (hμ'₂ : ∀ z : ℍ, μ' (Triangle.generatorTwoSL • z) = 1 + μ' z / (τ z : ℂ))
    (hμc : CuspRegular μ) (hμ'c : CuspRegular μ')
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = -F z / (τ z : ℂ))
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))
    (hFzero : ∀ z : ℍ, F z = 0 ↔
      triangleOrbitProjection z = triangleOrbitCenterOne ∨
        triangleOrbitProjection z = triangleOrbitCenterTwo)
    (hForder₁ : analyticOrderAt (F ∘ ofComplex) (Triangle.centerOne : ℂ) = 2)
    (hForder₂ : analyticOrderAt (F ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1)
    (hFcusp : ∃ v : ℂ → ℂ, AnalyticAt ℂ v 0 ∧ v 0 ≠ 0 ∧
      ∀ᶠ z in atImInfty, F z = (Triangle.cuspQ z)⁻¹ * v (Triangle.cuspQ z)) :
    μ = μ' := by
  obtain ⟨hν₁, hν₂⟩ := affine_sub_homogeneous hμ₁ hμ₂ hμ'₁ hμ'₂
  exact sub_eq_zero.mp (homogeneous_eq_zero_of_cuspRegular hτ hτc (hμ.sub hμ')
    hν₁ hν₂ (hμc.sub hμ'c) hF hF₁ hF₂ hFzero hForder₁ hForder₂ hFcusp)

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
