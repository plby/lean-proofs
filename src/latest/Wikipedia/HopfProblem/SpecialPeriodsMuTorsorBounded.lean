import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorUniqueness
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Boundedness and regularity at the actual triangle cusp

For a holomorphic function invariant under the actual cusp generator,
boundedness at imaginary infinity is equivalent to an analytic germ in
the actual normalized cusp coordinate.  The implication from boundedness
uses the genuine width-periodic cusp function and its removable-singularity
theorem.  The reverse implication follows from the cusp coordinate tending
to zero, without requiring periodicity or global holomorphicity.
-/

noncomputable section

open Filter Function Set UpperHalfPlane
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

/-- An actual analytic cusp germ makes a function bounded sufficiently
high in the upper half-plane.  No periodicity is needed in this direction. -/
theorem CuspRegular.bounded {f : ℍ → ℂ} (hf : CuspRegular f) :
    IsBoundedAtImInfty f := by
  obtain ⟨M, hM, he⟩ := hf
  have he' : f =ᶠ[atImInfty] fun z => M (Triangle.cuspQ z) := he
  have ht : Tendsto f atImInfty (𝓝 (M 0)) :=
    (hM.continuousAt.tendsto.comp
      (Triangle.cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds)).congr' he'.symm
  exact ht.isBigO_one ℝ

/-- The actual clockwise cusp generator translates by minus the width.
Its invariance supplies a positive complex period of the ambient function,
including the constant fallback of `ofComplex` outside the upper half-plane. -/
theorem periodic_comp_ofComplex_of_cusp_invariant {f : ℍ → ℂ}
    (hc : ∀ z : ℍ, f (triangleGeometricRepresentation triangleCuspGenerator z) = f z) :
    Function.Periodic (f ∘ ofComplex) (Triangle.width : ℂ) := by
  intro z
  by_cases hz : 0 < z.im
  · have hzw : 0 < (z + (Triangle.width : ℂ)).im := by simpa using hz
    have he : triangleGeometricRepresentation triangleCuspGenerator
        (ofComplex (z + (Triangle.width : ℂ))) = ofComplex z := by
      apply UpperHalfPlane.ext
      rw [triangleGeometricRepresentation_cusp_coe,
        ofComplex_apply_of_im_pos hzw, ofComplex_apply_of_im_pos hz]
      change z + (Triangle.width : ℂ) - Triangle.width = z
      ring
    exact (hc (ofComplex (z + (Triangle.width : ℂ)))).symm.trans (congrArg f he)
  · have hz' : z.im ≤ 0 := le_of_not_gt hz
    have hzw : (z + (Triangle.width : ℂ)).im ≤ 0 := by simpa using hz'
    exact congrArg f (ofComplex_apply_eq_of_im_nonpos hzw hz')

/-- The actual positive cusp width and its proved period allow the
bounded holomorphic function to extend analytically across `q = 0`. -/
theorem cuspRegular_of_bounded {f : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hc : ∀ z : ℍ, f (triangleGeometricRepresentation triangleCuspGenerator z) = f z)
    (hb : IsBoundedAtImInfty f) : CuspRegular f := by
  have hp := periodic_comp_ofComplex_of_cusp_invariant hc
  refine ⟨UpperHalfPlane.cuspFunction Triangle.width f,
    UpperHalfPlane.analyticAt_cuspFunction_zero Triangle.width_pos hp
      (hf.mdifferentiable (by simp)) hb, Filter.Eventually.of_forall ?_⟩
  intro z
  exact (UpperHalfPlane.eq_cuspFunction z Triangle.width_ne_zero hp).symm

/-- The analytic cusp condition in the quotient construction is exactly
the source's boundedness condition for actual cusp-invariant holomorphic functions. -/
theorem cuspRegular_iff_bounded {f : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hc : ∀ z : ℍ, f (triangleGeometricRepresentation triangleCuspGenerator z) = f z) :
    CuspRegular f ↔ IsBoundedAtImInfty f :=
  ⟨CuspRegular.bounded, cuspRegular_of_bounded hf hc⟩

/-- The source's two affine μ laws force invariance under the actual
cusp generator, without a separate cusp-periodicity assumption. -/
theorem affine_cusp_invariant {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτc : TauCovariant τ)
    (hμ₁ : ∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (hμ₂ : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (z : ℍ) : μ (triangleGeometricRepresentation triangleCuspGenerator z) = μ z := by
  have hprod (w : ℍ) :
      μ (triangleGeometricRepresentation (triangleGenerator₁ * triangleGenerator₂) w) = μ w := by
    rw [map_mul, Equiv.Perm.mul_apply, triangleGeometricRepresentation_generator₁_apply,
      triangleGeometricRepresentation_generator₂_apply, hμ₁, hμ₂, hτc.2]
    field_simp [(τ w).ne_zero]
    ring
  have hp := hprod (triangleGeometricRepresentation triangleCuspGenerator z)
  have he : triangleGeometricRepresentation (triangleGenerator₁ * triangleGenerator₂)
      (triangleGeometricRepresentation triangleCuspGenerator z) = z := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, triangle_generators_cusp_relation, map_one]
    rfl
  rw [he] at hp
  exact hp.symm

/-- Uniqueness with precisely the source's boundedness condition at
imaginary infinity.  Cusp periodicity and analytic regularity are proved
from the actual affine laws and bounded holomorphic cusp-function theorem. -/
theorem affine_eq_of_bounded {τ : ℍ → ℍ} {μ μ' F : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ)
    (hμ' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ')
    (hμ₁ : ∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (hμ₂ : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (hμ'₁ : ∀ z : ℍ, μ' (Triangle.generatorOneSL • z) = (1 - μ' z) / (τ z : ℂ))
    (hμ'₂ : ∀ z : ℍ, μ' (Triangle.generatorTwoSL • z) = 1 + μ' z / (τ z : ℂ))
    (hμb : IsBoundedAtImInfty μ) (hμ'b : IsBoundedAtImInfty μ')
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
  exact affine_eq_of_cuspRegular hτ hτc hμ hμ' hμ₁ hμ₂ hμ'₁ hμ'₂
    (cuspRegular_of_bounded hμ (affine_cusp_invariant hτc hμ₁ hμ₂) hμb)
    (cuspRegular_of_bounded hμ' (affine_cusp_invariant hτc hμ'₁ hμ'₂) hμ'b)
    hF hF₁ hF₂ hFzero hForder₁ hForder₂ hFcusp

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
